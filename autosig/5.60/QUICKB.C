#pragma inline

/*
   QUICKB.C - Quick B Protocol Support routines

 	originally converted to C by Paul M. Resch
	heavly modified by John Bridges
 */

/*
  This module implements the B-Protocol Functions.

  bp_DLE should be invoked whenever a <DLE> is received.
  bp_ENQ should be called whenever an <ENQ> is received.
  bp_ESC_I should be called when the sequence <ESC><I> is received.

  cgetc is an external procedure which returns a character from the
 	communications port or -1 if no character is received within the time
 	specified (in tenths of seconds).
  cputc is an external procedure which sends a character to the communication
 	port.
  create is an external procedure which creates the named file.
  open is an external procedure which opens the named file for input, and
 	returns a handle for the file.
  close is an external procedure which closes the file specified by handle.
  read is an external procedure which reads the specified number of bytes
 	from the file specified by handle, and returns the number of bytes
 	actually read, or a negative error.
  write is an external procedure which writes the specified number of bytes
 	to the file specified by handle.
  user_abort is an external procedure which is TRUE if the user wants to stop.

  This source was originally derived from QUICKB.INC, version 121687, written
  by Russ Ranshaw, CompuServe Incorporated.

 */

#define	TRUE	1
#define	FALSE	0

#define	DLE		16
#define	ETX		03
#define	NAK		21
#define	ENQ		05
#define	CR		0x0D
#define	LF		0x0A
#define	MAX_BUF_SIZE	1032		/* Largest data block we can handle */
#define	MAX_SA		2		/* Maximum number of waiting packets */

#define	DEF_BUF_SIZE	511		/* Default data block	 */
#define	DEF_WS		1		/* I can send 2 packets ahead */
#define	DEF_WR		1		/* I can receive single send-ahead  */
#define	DEF_BS		8		/* I can handle 1024 bytes	  */
#define	DEF_CM		1		/* I can handle CRC		 */
#define	DEF_DQ		1		/* I can handle non-quoted NUL */

#define	MAX_ERRORS	10


/* Receive States */

#define	R_GET_DLE	0
#define	R_GET_B		1
#define	R_GET_SEQ	2
#define	R_GET_DATA	3
#define	R_GET_CHECKSUM	4
#define	R_SEND_ACK	5
#define	R_TIMED_OUT	6
#define	R_SUCCESS	7

/* Send States */

#define	S_GET_DLE	1
#define	S_GET_NUM	2
#define	S_HAVE_ACK	3
#define	S_GET_PACKET	4
#define	S_TIMED_OUT	5
#define	S_SEND_NAK	6
#define	S_SEND_ENQ	7
#define	S_SEND_DATA	8

typedef	struct	PACKETB {
	int seq;	/* Packet's sequence number  */
	int num;	/* Number of bytes in packet */
	unsigned char buf[MAX_BUF_SIZE]; /* Actual packet data */
	} PACKET;

static PACKET	SA_Buf[MAX_SA+1];  /* Send-ahead buffers */

/* Table of control characters that need to be masked */

static char mask_table[]={
		0, 0, 0, 1, 0, 1, 0, 0,	/* NUL SOH SOB ETX EOT ENQ SYN BEL */
		0, 0, 0, 0, 0, 0, 0, 0,	/* BS  HT  LF  VT  FF  CR  SO  SI  */
		1, 1, 0, 1, 0, 1, 0, 0,	/* DLE DC1 DC2 DC3 DC4 NAK ^V  ^W  */
		0, 0, 0, 0, 0, 0, 0, 0};  /* CAN ^Y  ^Z  ESC ?	?	?	? */

static char hex_digit[]="0123456789ABCDEF";

static int seq_num;	/* Current Sequence Number - init by Term_ENQ */
static int checksum;	/* May hold CRC */
static int r_size;			/* size of receiver buffer */
static unsigned int s_counter,r_counter;
static int timed_out;	/* we timed out before receiving character */
static int cchar;			  /* current character */
static int masked;		/* TRUE if ctrl character was 'masked' */
static int packet_received;	/* True if a packet was received */
static unsigned char r_buffer[MAX_BUF_SIZE];

	 /* Other End's Parameters */
static char His_WS;			/* Sender's Window Send */
static char His_WR;			/* Sender's Window Receive  */
static char His_BS;			/* Sender's Block Size */
static char His_CM;		/* Sender's Check Method */

	 /* Negotiated Parameters */
static char Our_WS;			/* Negotiated Window Send */
static char Our_WR;			/* Negotiated Window Receive */
static char Our_BS;			/* Negotiated Block Size */
static char Our_CM;			/* Negotiated Check Method */

static int Quick_B;		/* True if Quick B in effect */
static int Use_CRC;		/* True if CRC in effect */
static int buffer_size;		/* Our_BS * 4	 */
static int SA_Max;			/* 1 if SA not enabled, else MAX_SA */
static int SA_Enabled;		/* True if Send-Ahead is permitted  */
static int ack_SA;		/* Which SA_Buf is waiting for an ACK */
static int fill_SA;	/* Which SA_Buf is ready for new data */
static int SA_Waiting;		/* Number of SA_Buf's waiting for ACK */
static int Aborting;		/* TRUE if aborting transfer */

/* Update the checksum/CRC */

static void do_checksum(c)
int c;
{
	if(Quick_B && Use_CRC)
		checksum=upd_CRC(c);
	else
	{
		checksum=checksum << 1;

		if(checksum > 255)
			checksum=(checksum & 0xFF)+ 1;

		checksum=checksum + c;

		if(checksum > 255)
			checksum=(checksum & 0xFF)+ 1;
	}
}

static void send_failure(code)
int code;
{
	register PACKET	*p;

	ack_SA=0;
	fill_SA=0;
	SA_Waiting=0;
	Aborting=TRUE;		/* inform get_ACK we're aborting */

	p=&SA_Buf[0];
	p->buf[0]='F';
	p->buf[1]=code;

	if(send_packet(1))
		SA_Flush();	/* Gotta wait for the host to ACK it */
}

/*
 * bp_ENQ is called when the terminal emulator receives the character <ENQ>
 * from the host.  Its purpose is to initialize for B Protocol and tell the
 * host that we support Quick B.
 */

void bp_ENQ()
{
	seq_num=0;
	buffer_size=DEF_BUF_SIZE;	/* Set up defaults */
	Quick_B	=FALSE;		/* Not Quick B Protocol */
	Use_CRC	=FALSE;		/* Not CRC_16 */
	SA_Enabled =FALSE;		/* No Send-Ahead by us */
	SA_Max	=1;		 /*=single packet sent */

	cputc(DLE);
	cputc('+');

	cputc(DLE);
	cputc('0');
}

/*
 * bp_ESC_I is called when <ESC><I> is received by the terminal emulator.
 * Note that Quick B allows +XX to be added to the end of the response, where
 * XX is the two hex digits of the standard B Protocol checksum of the
 * preceeding characters in the response.
 */
static char esc_I_response[]="#VCO,PB,DT,+";

void bp_ESC_I()
{
	int save_Use_CRC;
	register int i;

	save_Use_CRC=Use_CRC;
	Use_CRC=FALSE;
	checksum=0;

	i=0;
	while(esc_I_response[i])
	{
		cputc(esc_I_response[i]);
		do_checksum(esc_I_response[i]);
		i++;
	}

/* Append two hex digits of checksum to response */

	cputc(hex_digit[(checksum >> 4)& 0x0F ]);
	cputc(hex_digit[ checksum & 0x0F ]);
	cputc(CR);

	Use_CRC=save_Use_CRC;
}


static void send_masked_byte(c)
int c;
{
	c&=0xff;
	if(c<32)
	{
		if(mask_table[c]!=0)
		{
			cputc(DLE);
			cputc(c+'@');
		}
		else
			cputc(c);
	}
	else
		cputc(c);

	s_counter=(s_counter+1)&DEF_BUF_SIZE;
}

static void send_ack()
{
	cputc(DLE);
	cputc(seq_num + '0');
}

static void send_nak()
{
	cputc(NAK);
}


static void send_enq()
{
	cputc(ENQ);
}

static int read_byte()
{
	timed_out=FALSE;

	cchar=cgetc(100);

	if(cchar < 0)
		return(FALSE);

	r_counter=(r_counter+1)&DEF_BUF_SIZE;
	return(TRUE);
}


static int read_masked_byte()
{
	masked=FALSE;

	if(read_byte()==FALSE)
		return(FALSE);

	if(cchar==DLE)
	{
		if(read_byte()==FALSE)
			return(FALSE);
		cchar &=0x1F;
		masked=TRUE;
	}

	return(TRUE);
}

/* Increment Sequence Number */

static int incr_seq(value)
int value;
{
	return(value==9 ? 0 : value + 1);
}

/*	Lead_in_Seen is TRUE if the <DLE><B> has been seen already.
	from_send_packet is TRUE if called from Send_Packet
	(causes exit on first error detected)
	Returns True if packet is available from host. */

static int read_packet(lead_in_seen,from_send_packet)
int lead_in_seen,from_send_packet;
{
	int State,next_seq,block_num,errors,new_cks;
	int i;

	packet_received=FALSE;
	for(i=0; i<buffer_size; i++)
		r_buffer[i]=0;
	next_seq=(seq_num+1)%10;
	errors=0;

	if(lead_in_seen)		/* Start off on the correct foot */
		State=R_GET_SEQ;
	else
		State=R_GET_DLE;

	while(TRUE)
	{
		switch (State){
		case R_GET_DLE :
			if(user_abort())
			{
				send_failure('A');
				return(FALSE);
			}

			if(!read_byte())
					State=R_TIMED_OUT;
			else if((cchar & 0x7F)==DLE)
					State=R_GET_B;
			else if((cchar & 0x7F)==ENQ)
				State=R_SEND_ACK;
			break;

		case R_GET_B :
			if(!read_byte())
				State=R_TIMED_OUT;
			else if((cchar & 0x7F)=='B')
				State=R_GET_SEQ;
			else if(cchar==ENQ)
				State=R_SEND_ACK;
			else
				State=R_GET_DLE;
			break;

		case R_GET_SEQ :
			if(!read_byte())
				State=R_TIMED_OUT;
			else if(cchar==ENQ)
				State=R_SEND_ACK;
			else
			{
				if(Quick_B && Use_CRC)
					checksum=init_CRC(-1);
				else checksum=0;

				block_num=cchar - '0';

				do_checksum(cchar);

				i=0;
				State=R_GET_DATA;
			}
			break;

		case R_GET_DATA :
			r_counter=0;
			if(!read_masked_byte())
				State=R_TIMED_OUT;
			else if((cchar==ETX)&& !masked)
			{
				do_checksum(ETX);
				State=R_GET_CHECKSUM;
			}
			else
			{
				r_buffer[i]=cchar;
				i=i + 1;
				do_checksum(cchar);
			}
			break;

		case R_GET_CHECKSUM :
			if(!read_masked_byte())
				State=R_TIMED_OUT;
			else
			{
				if(Quick_B && Use_CRC)
				{
					checksum=upd_CRC(cchar);

					if(!read_masked_byte())
						new_cks=checksum ^ 0xFF;
					else
					{
						checksum=upd_CRC(cchar);
						new_cks=0;
					}
				}
				else new_cks=cchar;

				if(new_cks !=checksum)
					State=R_TIMED_OUT;
				else if(r_buffer[0]=='F')/* Watch for Failure Packet */
					State=R_SUCCESS;	/* which is accepted regardless */
				else if(block_num==seq_num)	/* Watch for duplicate block */
					State=R_SEND_ACK;
				else if(block_num !=next_seq)
					State=R_TIMED_OUT;	/* Bad sequence number */
				else
					State=R_SUCCESS;
			}
			break;

		case R_TIMED_OUT :
			errors=errors + 1;

			if((errors > MAX_ERRORS)||(from_send_packet))
				return(FALSE);

			send_nak();

			if(from_send_packet)
				return(FALSE);

			State=R_GET_DLE;
			break;

		case R_SEND_ACK :
			send_ack();
			State=R_GET_DLE;	/* wait for the next block */
			break;

		case R_SUCCESS :
			seq_num=block_num;
			r_size=i;
			packet_received=TRUE;
			return(TRUE);
		}
	}
}

static void send_data(Buffer_Number)
int Buffer_Number;
{
	int i;
	register PACKET	*p;

	s_counter=0;
	p=&SA_Buf[Buffer_Number];
	if(Quick_B && Use_CRC)
		checksum=init_CRC(-1);
	else
		checksum=0;

	cputc(DLE);
	cputc('B');

	cputc(p->seq + '0');
	do_checksum(p->seq + '0');

	for(i=0; i<=p->num; i++)
	{
		send_masked_byte(p->buf[i]);
		do_checksum(p->buf[i]);
	}

	cputc(ETX);
	do_checksum(ETX);

	if(Quick_B && Use_CRC)
		send_masked_byte(checksum >> 8);

	send_masked_byte(checksum);
}

static int incr_SA(old_value)
int old_value;
{
	return(old_value==MAX_SA ? 0 : old_value + 1);
}

/*
 * ReSync is called to restablish syncronism with the remote.  This is
 * accomplished by sending <ENQ><ENQ> and waiting for the sequence
 * <DLE><d><DLE><d> to be received, ignoring everything else.
 *
 * Return is -1 on time out, else the digit <d>.
 */
#define	GET_FIRST_DLE		1
#define	GET_FIRST_DIGIT		2
#define	GET_SECOND_DLE		3
#define	GET_SECOND_DIGIT	4

static int ReSync()
{
	int State,Digit_1;

	cputc(ENQ);	/* Send <ENQ><ENQ> */
	cputc(ENQ);
	State=GET_FIRST_DLE;

	while(1)
	{
		switch(State){
		case GET_FIRST_DLE :
			if(!read_byte())
				return(-1);
			if(cchar==DLE)
				State=GET_FIRST_DIGIT;
			break;
		case GET_FIRST_DIGIT :
			if(!read_byte())
				return(-1);
			if((cchar >='0')&&(cchar <='9'))
			{
				Digit_1=cchar;
				State=GET_SECOND_DLE;
			}
			break;
		case GET_SECOND_DLE :
			if(!read_byte())
				return(-1);
			if(cchar==DLE)
				State=GET_SECOND_DIGIT;
			break;
		case GET_SECOND_DIGIT :
			if(!read_byte())
				return(-1);
			if((cchar >='0')&&(cchar <='9'))
			{
				if(Digit_1==cchar)
					return(cchar);
				else
				{
					Digit_1=cchar;
					State=GET_SECOND_DLE;
				}
			}
			else
				State=GET_SECOND_DLE;
			break;
		}
	}
}

/*
 * get_ACK is called to wait until the SA_Buf indicated by ack_SA
 * has been ACKed by the host.
 */
static int get_ACK()
{
	int State,errors,block_num,i;
	int Sent_ENQ;
	int SA_Index;

	packet_received=FALSE;
	errors=0;
	Sent_ENQ=FALSE;
	State=S_GET_DLE;

	while(TRUE)
	{
		switch(State){
		case S_GET_DLE :
			if(user_abort())
			{
				send_failure('A');
				return(FALSE);
			}

			if(!read_byte())
				State=S_TIMED_OUT;
			else if(cchar==DLE)
				State=S_GET_NUM;
			else if(cchar==NAK)
			{
				if(++errors > MAX_ERRORS)
					return(FALSE);
				State=S_SEND_ENQ;
			}
			else if(cchar==ETX)
				State=S_SEND_NAK;
			break;

		case S_GET_NUM :
			if(!read_byte())
				State=S_TIMED_OUT;
			else if((cchar >='0')&&(cchar <='9'))
				State=S_HAVE_ACK;	/* Received ACK */
			else if(cchar=='B')
				State=S_GET_PACKET; /* Try to get packet */
			else if(cchar==NAK)
			{
				if(++errors > MAX_ERRORS)
					return(FALSE);
				State=S_SEND_ENQ;
			}
			else
				State=S_TIMED_OUT;
			break;

		case S_GET_PACKET :
			if(read_packet(TRUE,TRUE))
			{
				if(r_buffer[0]=='F')
				{
					send_ack();
					return(FALSE);
				}
				else
					return(TRUE);
			}

			State=S_TIMED_OUT; /* On a bad receive, try again */
			break;
		case S_HAVE_ACK:
			block_num=cchar - '0';
			if(SA_Buf[ack_SA].seq==block_num)
			{	/* This is the one we're waiting for */
				ack_SA=incr_SA(ack_SA);
				SA_Waiting--;
				return(TRUE);
			}
			else if(SA_Buf[incr_SA(ack_SA)].seq==block_num &&
				(SA_Waiting==2))
			{	/* Must have missed an ACK */
				ack_SA=incr_SA(ack_SA);
				ack_SA=incr_SA(ack_SA);
				SA_Waiting -=2;
				return(TRUE);
			}
			else if(SA_Buf[ack_SA].seq==incr_seq(block_num))
			{
				if(Sent_ENQ)
					State=S_SEND_DATA;
				else
					State=S_GET_DLE;
			}
			else
				State=Aborting ? S_GET_DLE : S_TIMED_OUT;
			Sent_ENQ=FALSE;
			break;
		case S_TIMED_OUT :
			if(++errors > MAX_ERRORS)
				return(FALSE);
			else
			{
				if(Aborting &&(errors > 3))
					return(FALSE);
			}
			State=S_SEND_ENQ;
			break;

		case S_SEND_NAK :
			if(++errors > MAX_ERRORS)
				return(FALSE);

			send_nak();

			State=S_GET_DLE;
			break;

		case S_SEND_ENQ :
			if(++errors > MAX_ERRORS)
				return(FALSE);
			cchar=ReSync();
			if(cchar==-1)
				State=S_SEND_ENQ;
			else
				State=S_HAVE_ACK;
			Sent_ENQ=TRUE;
			break;

		case S_SEND_DATA :
			SA_Index=ack_SA;

			for(i=1; i<=SA_Waiting; i++)
			{
				send_data(SA_Index);
				SA_Index=incr_SA(SA_Index);
			}

			State=S_GET_DLE;
			Sent_ENQ=FALSE;
			break;
		}
	}
} /* get_ACK */

static int send_packet(size)
int size;
{
	if(SA_Waiting==SA_Max)
		if(!get_ACK())
			return(FALSE);

	seq_num=incr_seq(seq_num);
	SA_Buf[fill_SA].seq=seq_num;
	SA_Buf[fill_SA].num=size;
	send_data(fill_SA);
	fill_SA=incr_SA(fill_SA);
	SA_Waiting=SA_Waiting + 1;
	return(TRUE);
}
/*
 * SA_Flush is called after sending the last packet to get host's
 * ACKs on outstanding packets.
 */
static int SA_Flush()
{
	while(SA_Waiting > 0)
		if(!get_ACK())
			return(FALSE);
	return(TRUE);
}

#define tval (*(unsigned long far *)0x0040006cl)

/* Send_File is called to send a file to the host */
static int send_file(name)
char name[];
{
	int fd,bknum,cps,n;
	long oldt,pos;
	unsigned long filelen;
	register PACKET	*p;

	sput("Sending \"");
	sput(name);
	sput("\"\r\n");

	fd=open(name);
	if(fd<=0)
  	{
		sput("\r\n** Cannot find that file **\r\n");
		send_failure('E');
		return(FALSE);
	}

	filelen=lseek(fd,0l,2);
	lseek(fd,0l,0);

	oldt=tval;
	bknum=1;
	sput("\r\n");
	do
	{
		p=&SA_Buf[fill_SA];
		p->buf[0]='N';
		n=read(fd,(long)buffer_size,&p->buf[1]);
		if(n>0)
		{
			sput("Block #");
			putint(bknum,4);
			sput(", ");
			if(send_packet(n)==FALSE)
				return(FALSE);
			++bknum;
			pos=lseek(fd,0l,1);
			putlint(pos,9);
			sput(" Bytes, at ");
			if(tval<oldt)
				oldt-=1573040l;
			cps=((pos*4661l)/(tval-oldt))>>8;
			putint(cps,4);
			sput("cps ");
			putint((int)((100*pos)/filelen),3);
			sput("% Complete\r");
		}
	} while(n==buffer_size);

	close(fd);

	if(n < 0)
	{
		send_failure('E');
		sput("\r\n** Read failure...aborting **\r\n");
		return(FALSE);
	}

/* Inform host that the file was sent */
	p=&SA_Buf[fill_SA];
	p->buf[0]='T';
	p->buf[1]='C';

	if(send_packet(2)==FALSE)
		return(FALSE);
	else
	{
		sput("\r\nWaiting for host...\r\n");
		if(!SA_Flush())
			return(FALSE);
		return(TRUE);
	}
}

/*
 * do_transport_parameters is called when a Packet type of + is received.
 * It sends a packet of our local Quick B parameters and sets the Our_xx
 * parameters to the minimum of the sender's and our own parameters.
 */
static do_transport_parameters()
{
	register PACKET	*p;

	His_WS=r_buffer[1];	/* Pick out Sender's parameters */
	His_WR=r_buffer[2];
	His_BS=r_buffer[3];
	His_CM=r_buffer[4];

	p=&SA_Buf[fill_SA];
	p->buf[0]='+';  /* Prepare to return our own parameters */
	p->buf[1]=DEF_WS;
	p->buf[2]=DEF_WR;
	p->buf[3]=DEF_BS;
	p->buf[4]=DEF_CM;
	p->buf[5]=DEF_DQ;

	if(!send_packet(5))
		return;

	if(SA_Flush())		 /* Wait for host's ACK on our packet */
	{
/* Take minimal subset of Transport Params. */
/* If he can send ahead, we can receive it. */
		Our_WR=(His_WS < DEF_WR)? His_WS : DEF_WR;

/* If he can receive send ahead, we can send it. */
		Our_WS=(His_WR < DEF_WS)? His_WR : DEF_WS;

		Our_BS=His_BS < DEF_BS ? His_BS : DEF_BS;

		Our_CM=His_CM < DEF_CM ? His_CM : DEF_CM;

		if(Our_BS==0)
			Our_BS=4;	/* Default */

		buffer_size=Our_BS * 128;

		Quick_B=TRUE;

		if(Our_CM==1)
			Use_CRC=TRUE;

		if(Our_WS !=0)
		{
			SA_Enabled=TRUE;
			SA_Max	=MAX_SA;
		}
	}
}

/*
  do_application_parameters is called when a ? packet is received.
  This version ignores the host's packet and returns a ? packet
  saying that normal B Protocol File Transfer is supported.
 (Well, actually it says that no extended application packets are
	supported.  The T packet is assumed to be standard.)*/

static void do_application_parameters()
{
	register PACKET	*p;

	p=&SA_Buf[fill_SA];
	p->buf[0]='?';	/* Build the ? packet */
	p->buf[1]=1;		/* The T packet flag  */

	if(send_packet(1))		/* Send the packet */
		SA_Flush();
}

/* Receive_File is called to receive a file from the host */
static int receive_file(name)
char name[];
{
	int fd,bknum,cps;
	long oldt,pos;
	long bytes;

	sput("Receiving \"");
	sput(name);
	sput("\"\r\n");

	fd=create(name);
	if(fd<=0)
	{
		sput("\r\n** Cannot open file...aborting **\r\n");
		send_failure('E');
		return(FALSE);
	}

	sput("\r\n");
	send_ack();

	oldt=tval;
	bknum=1;

/* Process each incoming packet until 'TC' packet received or failure */
	while(TRUE)
	{
		sput("Block #");
		putint(bknum,4);
		sput(", ");
		if(read_packet(FALSE,FALSE))
		{
			switch(r_buffer[0])
			{
			case 'N' :
				bytes=r_size - 1;
				if(write(fd,bytes,&r_buffer[1])!=bytes)
				{
					sput("\r\n** Write failure...aborting **\r\n");
					close(fd);
					send_failure('E');
					return(FALSE);
				}
				send_ack();
				++bknum;
				pos=lseek(fd,0l,1);
				putlint(pos,9);
				sput(" Bytes, at ");
				if(tval<oldt)
					oldt-=1573040l;
				cps=((pos*4661l)/(tval-oldt))>>8;
				putint(cps,4);
				sput("cps\r");
				break;

			case 'T' :
				if(r_buffer[1]=='C')
				{
					close(fd);

					send_ack();
					return(TRUE);
				}
				else
				{
					sput("\r\n** Invalid termination packet...aborting **\r\n");
					close(fd);
					send_failure('N');
					return(FALSE);
				}

			case 'F' :
				send_ack();
				sput("\r\n** Failure packet received...aborting **\r\n");
				close(fd);
				return(FALSE);
			}
		}
	 	else
		{
			sput("\r\n** Failed to receive packet...aborting **\r\n");
			close(fd);
			return(FALSE);
		}
	}
}

/*
 * bp_DLE is called from the main program when the character <DLE> is
 * received from the host.
 *
 * This routine calls read_packet and dispatches to the appropriate
 * handler for the incoming packet.
 */
void bp_DLE()
{
	int i;
	char filename[255];
	char *pt;
/*
 * Begin by getting the next character.  If it is <B> then enter the
 * B_Protocol state.  Otherwise simply return.
 */

	if(cgetc(10)!='B')
		return;

	ack_SA=0;	/* Initialize Send-ahead variables */
	fill_SA=0;
	SA_Waiting=0;
	Aborting=FALSE;	/* not aborting ... yet */
/*  <DLE><B> received; begin B Protocol */

	r_counter=0;
	s_counter=0;

	sput("\r\n");
	if(Quick_B)
	{
		sput("*** Quick B is in effect ***\r\n");

		if(Use_CRC)
			sput("*** Using CRC ***\r\n");

		if(Our_WS!=0)	/* Allow send-ahead if other end agrees */
			sput("*** Send-Ahead enabled ***\r\n");
	}

	if(read_packet(TRUE,FALSE))
	{
/* Dispatch on the type of packet just received */

		switch(r_buffer[0])
		{
		case 'T':	/* File Transfer Application */
			switch(r_buffer[1])
			{
			case 'D' :	/* downloading */
				break;
			case 'U' :	/* uploading */
				break;
			default :
				send_failure('N');
				return;
			}

			switch(r_buffer[2])
			{
			case 'A':	/* ascii file */
				break;
			case 'B':	/* binary file */
				break;
			default :
				send_failure('N');	/* not implemented */
				return;
			}

			i=2;
			pt=filename;
			while((r_buffer[i]!=0)&&(i<r_size-1))
				*pt++=r_buffer[++i];

			*pt='\0';

			if(r_buffer[1]=='U')
				i=send_file(filename);
			else
				i=receive_file(filename);

			sput("\r\n");
			if(i)
				sput("\r\nTransfer successfully completed!\r\n");
			break;

		case '+':	  /* Received Transport Parameters Packet */
			do_transport_parameters();
			break;

		case '?':	  /* Received Application Parameters Packet */
			do_application_parameters();
			break;

		default:	/* Unknown packet; tell host we don't know */
			send_failure('N');
				break;

		}  /* of case */
	}	/* of if read_packet the */
}


