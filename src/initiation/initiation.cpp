/*
Copyright (C) 2016 Zidan Zhang <zidan.zhang@kuleuven.be>
                   Jing Lv <lvjingmaoyi@tju.edu.cn>

This file is distributed under free software licence:
you can redistribute it and/or modify it under the terms of the
GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

//This program is used to generate the initial simulation box for divinyl Controlled Chain Growth project
#include "math.h"
#include "stdio.h"
#include "stdlib.h"
#include "time.h"

///////////////////////////
#define nmon      150480                   // Number of monomers
#define nrchain   1520                     // Number of chains (active radical + dormant radical chains)
#define nactiR    1                        // Number of active radicals
#define ndormR    1519                     // Number of dormant radicals
#define ntot      (nmon+nrchain)           // Total number of particles

#define lsx       200                      // length of the simulation box vector for X axis
#define lsy       200
#define lsz       200


int ipx[lsx+1],ipx2[lsx+1],imx[lsx+1];        // ipx, ipx2, imx are the x positions of mono opposite particle, positive move of mono and the negative move of mono.
int ipy[lsy+1],ipy2[lsy+1],imy[lsy+1];
int ipz[lsz+1],ipz2[lsz+1],imz[lsz+1];
int monlatp[ntot+1][3+1],montype[ntot+1];     // coordinate of a site of every particle    
int monlinks[ntot+1][4+1],monbd[ntot+1][4+1]; // mono1 2 3 4 which linked with mono; type of bonds which formed with mono
int numbonds[ntot+1],monreactive[ntot+1];     // how many bonds are formed with every particle
int latt[lsx+1][lsy+1][lsz+1];                // latt number of every site in the lattice (sol is 0, particle is 1 2...)
int MCS=10000,mcs;
int mono;

////////////////////////random generator///////////////////////
 /* Period parameters */
#define NNNN 624
#define MMMM 397
#define MATRIX_A 0x9908b0dfUL   /* constant vector a */
#define UMASK 0x80000000UL /* most significant w-r bits */
#define LMASK 0x7fffffffUL /* least significant r bits */
#define MIXBITS(u,v) ( ((u) & UMASK) | ((v) & LMASK) )
#define TWIST(u,v) ((MIXBITS(u,v) >> 1) ^ ((v)&1UL ? MATRIX_A : 0UL))

static unsigned long randstate[NNNN]; /* the array for the state vector  */
static int randleft = 1;
static int randinitf = 0;
static unsigned long *randnext;

/* initializes randstate[NNNN] with a seed */
void init_genrand(unsigned long s)
{
    int j;
    randstate[0]= s & 0xffffffffUL;
    for (j=1; j<NNNN; j++) {
        randstate[j] = (1812433253UL * (randstate[j-1] ^ (randstate[j-1] >> 30)) + j); 
        /* See Knuth TAOCP Vol2. 3rd Ed. P.106 for multiplier. */
        /* In the previous versions, MSBs of the seed affect   */
        /* only MSBs of the array randstate[].                        */
        /* 2002/01/09 modified by Makoto Matsumoto             */
        randstate[j] &= 0xffffffffUL;  /* for >32 bit machines */
    }
    randleft = 1; randinitf = 1;
}

/* initialize by an array with array-length */
/* init_key is the array for initializing keys */
/* key_length is its length */
void init_by_array(unsigned long init_key[], unsigned long key_length)
{
    int i, j, k;
    init_genrand(19650218UL);
    i=1; j=0;
    k = (NNNN>key_length ? NNNN : key_length);
    for (; k; k--) {
        randstate[i] = (randstate[i] ^ ((randstate[i-1] ^ (randstate[i-1] >> 30)) * 1664525UL))
          + init_key[j] + j; /* non linear */
        randstate[i] &= 0xffffffffUL; /* for WORDSIZE > 32 machines */
        i++; j++;
        if (i>=NNNN) { randstate[0] = randstate[NNNN-1]; i=1; }
        if (j>=key_length) j=0;
    }
    for (k=NNNN-1; k; k--) {
        randstate[i] = (randstate[i] ^ ((randstate[i-1] ^ (randstate[i-1] >> 30)) * 1566083941UL))
          - i; /* non linear */
        randstate[i] &= 0xffffffffUL; /* for WORDSIZE > 32 machines */
        i++;
        if (i>=NNNN) { randstate[0] = randstate[NNNN-1]; i=1; }
    }

    randstate[0] = 0x80000000UL; /* MSB is 1; assuring non-zero initial array */ 
    randleft = 1; randinitf = 1;
}

static void randnext_state(void)
{
    unsigned long *p=randstate;
    int j;

    /* if init_genrand() has not been called, */
    /* a default initial seed is used         */
    if (randinitf==0) init_genrand(5489UL);

    randleft = NNNN;
    randnext = randstate;
    
    for (j=NNNN-MMMM+1; --j; p++) 
        *p = p[MMMM] ^ TWIST(p[0], p[1]);

    for (j=MMMM; --j; p++) 
        *p = p[MMMM-NNNN] ^ TWIST(p[0], p[1]);

    *p = p[MMMM-NNNN] ^ TWIST(p[0], randstate[0]);
}

/* generates a random number on [0,0xffffffff]-interval */
unsigned long genrand_int32(void)
{
    unsigned long y;

    if (--randleft == 0) randnext_state();
    y = *randnext++;

    /* Tempering */
    y ^= (y >> 11);
    y ^= (y << 7) & 0x9d2c5680UL;
    y ^= (y << 15) & 0xefc60000UL;
    y ^= (y >> 18);

    return y;
}

/* generates a random number on [0,0x7fffffff]-interval */
long genrand_int31(void)
{
    unsigned long y;

    if (--randleft == 0) randnext_state();
    y = *randnext++;

    /* Tempering */
    y ^= (y >> 11);
    y ^= (y << 7) & 0x9d2c5680UL;
    y ^= (y << 15) & 0xefc60000UL;
    y ^= (y >> 18);

    return (long)(y>>1);
}

/* generates a random number on [0,1]-real-interval */
double genrand_real1(void)
{
    unsigned long y;

    if (--randleft == 0) randnext_state();
    y = *randnext++;

    /* Tempering */
    y ^= (y >> 11);
    y ^= (y << 7) & 0x9d2c5680UL;
    y ^= (y << 15) & 0xefc60000UL;
    y ^= (y >> 18);

    return (double)y * (1.0/4294967295.0); 
    /* divided by 2^32-1 */ 
}

/* generates a random number on [0,1)-real-interval */
double genrand_real2(void)
{
    unsigned long y;

    if (--randleft == 0) randnext_state();
    y = *randnext++;

    /* Tempering */
    y ^= (y >> 11);
    y ^= (y << 7) & 0x9d2c5680UL;
    y ^= (y << 15) & 0xefc60000UL;
    y ^= (y >> 18);

    return (double)y * (1.0/4294967296.0); 
    /* divided by 2^32 */
}

/* generates a random number on (0,1)-real-interval */
double genrand_real3(void)
{
    unsigned long y;

    if (--randleft == 0) randnext_state();
    y = *randnext++;

    /* Tempering */
    y ^= (y >> 11);
    y ^= (y << 7) & 0x9d2c5680UL;
    y ^= (y << 15) & 0xefc60000UL;
    y ^= (y >> 18);

    return ((double)y + 0.5) * (1.0/4294967296.0); 
    /* divided by 2^32 */
}

/* generates a random number on [0,1) with 53-bit resolution*/
double genrand_res53(void) 
{ 
    unsigned long a=genrand_int32()>>5, b=genrand_int32()>>6; 
    return(a*67108864.0+b)*(1.0/9007199254740992.0); 
} 
/* These real versions are from Isaku Wada, 2002/01/09 added */


int ini()
{
    int i, j, k, xp, yp, zp, xp1, yp1, zp1;
	int kk1, x_t, y_t, z_t;
           
	for(i=1;i<=lsx;i++)
        for(j=1;j<=lsy;j++)
            for(k=1;k<=lsz;k++)
                latt[i][j][k] = 0;  // Initially, all site are 0 which represents solvent

    kk1=0;                          // records the number of reactants in the latt

	while(1)    // true, continue
	{
        x_t = genrand_int32()%lsx/2+1;
	    y_t = genrand_int32()%lsy/2+1;
        z_t = genrand_int32()%lsz/2+1;
        if(latt[x_t][y_t][z_t]==0)
	    {
            kk1++;
            latt[x_t][y_t][z_t]=kk1;
	        monlatp[kk1][1]=x_t*2-1;
	        monlatp[kk1][2]=y_t*2-1;
	        monlatp[kk1][3]=z_t*2-1;
	    }
        if(kk1==ntot)
            break;

	}

	for(i=1;i<=ntot;i++)
	{
        if(i<=nactiR)   // active radical has three reactive bonds (react with other elements in the system)
		{	
			monbd[i][1]=0; monbd[i][2]=0; monbd[i][3]=0; monbd[i][4]=0;
		    monlinks[i][1]=0; monlinks[i][2]=0; monlinks[i][3]=0;
            numbonds[i]=0;
            montype[i]=1;
            monreactive[i]=3;
		}	
		else if (i>nactiR&&i<=nrchain)  // dormant radical has two reactive bonds
        {
            monbd[i][1]=0; monbd[i][2]=0; monbd[i][3]=0; monbd[i][4]=0;
            monlinks[i][1]=0; monlinks[i][2]=0;
            numbonds[i]=0;
            montype[i]=0;
            monreactive[i]=2;
        }
        else                           // monomers has four reactive bonds
        {
            monbd[i][1]=0; monbd[i][2]=0; monbd[i][3]=0; monbd[i][4]=0;
            monlinks[i][1]=0; monlinks[i][2]=0; monlinks[i][3]=0; monlinks[i][4]=0;
            numbonds[i]=0;
            montype[i]=2;
            monreactive[i]=4;
        }

	}

//******************************************************************
// Now we initialize the lattice, setting all occupied vertices to unity
//******************************************************************
    for(i=1;i<=lsx;i++)
        for(j=1;j<=lsy;j++)
            for(k=1;k<=lsz;k++)
                latt[i][j][k] = 0;

    for(j=1;j<=ntot;j++)
    {
        xp = monlatp[j][1];
        yp = monlatp[j][2];
        zp = monlatp[j][3];
        xp1 = ipx[xp];
        yp1 = ipy[yp];
        zp1 = ipz[zp];
        latt[xp][yp][zp] = j;
        latt[xp1][yp][zp] = j;
        latt[xp][yp1][zp] = j;
        latt[xp][yp][zp1] = j;
        latt[xp1][yp1][zp] = j;
        latt[xp1][yp][zp1] = j;
        latt[xp][yp1][zp1] = j;
        latt[xp1][yp1][zp1] = j;
    }
    return 0;
}

int bflout(int imcs)  //Stores the final configuration of the simulation into ini.dat file,imcs is the instantaneous value of mcs (1 to 10000)
{
    int i;
    FILE* fp;

    if((fp=fopen("ini.dat", "w+" )) == NULL)
        printf( "The file was not opened\n" ); 
    else
    {
        fprintf(fp,"%ld %ld %ld %ld\n", ntot,lsx,lsy,lsz);

        for(i=1;i<=ntot;i++)
        {
		    fprintf(fp,"%ld %ld %ld\n", monlatp[i][1],monlatp[i][2],monlatp[i][3]);

            fprintf(fp,"%ld %ld %ld %ld %ld %ld %ld %ld\n", monlinks[i][1],monlinks[i][2],monlinks[i][3],monlinks[i][4],monbd[i][1],monbd[i][2],monbd[i][3],monbd[i][4]);

			fprintf(fp,"%ld %ld %ld\n",montype[i],numbonds[i],monreactive[i]);	
        }
        fclose(fp);
    }

	if((fp=fopen("intstate.dat", "w+" )) == NULL)
        printf( "The file was not opened\n" );
    else
    {
        fprintf(fp,"%ld %ld\n",MCS,imcs);
        fclose(fp);
    }
return 0;
}

bool movement()
{
//***************************************************************
// Performs the actual Monte Carlo simulation using jumps to nearest-
// neighbor sites as the only type of moves.
//***************************************************************
    int  dir, xp, yp, zp;
    int xm1, xp1, xp2, ym1, yp1, yp2, zm1, zp1, zp2;
    int  testlat;

    dir = genrand_int32()%6 + 1; //select the moving direction

    xp = monlatp[mono][1];       //select the bead-"mono" (any element in the lattice) to move 
    yp = monlatp[mono][2];
    zp = monlatp[mono][3];

    xp1 = ipx[xp];
    yp1 = ipy[yp];
    zp1 = ipz[zp];

    switch( dir )
    {
        case 1:
        {// jump in +x direction
            xp2 = ipx2[xp];         //xp2=xp+2 or xp1+1
       
            testlat = latt[xp2][yp][zp] + latt[xp2][yp1][zp] + latt[xp2][yp][zp1] + latt[xp2][yp1][zp1];
            if(testlat==0)
            {// new monomer and radical positions 
                monlatp[mono][1] = xp1;
                // set the newly occupied vertices to mono and the old to zero.
                latt[xp2][yp][zp] = mono;
                latt[xp2][yp1][zp] = mono;
                latt[xp2][yp][zp1] = mono;
                latt[xp2][yp1][zp1] = mono;
                latt[xp][yp][zp] = 0;
                latt[xp][yp1][zp] = 0;
                latt[xp][yp][zp1] = 0;
                latt[xp][yp1][zp1] = 0;
                return true;
            }
            else
                return true;
        }
        break;
		
        case 6:
        {// jump in -x direction
            xm1 = imx[xp];
          
            testlat = latt[xm1][yp][zp] + latt[xm1][yp1][zp] + latt[xm1][yp][zp1] + latt[xm1][yp1][zp1];

            if(testlat==0)
		    {
                monlatp[mono][1] = xm1;
                
                latt[xm1][yp][zp] = mono;
                latt[xm1][yp1][zp] = mono;
                latt[xm1][yp][zp1] = mono;
                latt[xm1][yp1][zp1] = mono;
                latt[xp1][yp][zp] = 0;
                latt[xp1][yp1][zp] = 0;
                latt[xp1][yp][zp1] = 0;
                latt[xp1][yp1][zp1] = 0;
                return true;
		    }
		    else
			    return true;
		}
        break;
		
	    case 2:
        {// jump in +y direction
            yp2 = ipy2[yp];

            testlat = latt[xp][yp2][zp] + latt[xp1][yp2][zp] + latt[xp][yp2][zp1] + latt[xp1][yp2][zp1];

            if(testlat==0)
		    {
                monlatp[mono][2] = yp1;
                
                latt[xp][yp2][zp] = mono;
                latt[xp1][yp2][zp] = mono;
                latt[xp][yp2][zp1] = mono;
                latt[xp1][yp2][zp1] = mono;
                latt[xp][yp][zp] = 0;
                latt[xp1][yp][zp] = 0;
                latt[xp][yp][zp1] = 0;
                latt[xp1][yp][zp1] = 0;
                return true;
		    }
		    else
			    return true;
		}
        break;
		
	    case 5:
        {// jump in -y direction
            ym1 = imy[yp];
        
            testlat= latt[xp][ym1][zp] + latt[xp1][ym1][zp] + latt[xp][ym1][zp1] + latt[xp1][ym1][zp1];

            if(testlat==0)
			{
                monlatp[mono][2] = ym1;
                
                latt[xp][ym1][zp] = mono;
                latt[xp1][ym1][zp] = mono;
                latt[xp][ym1][zp1] = mono;
                latt[xp1][ym1][zp1] = mono;
                latt[xp][yp1][zp] = 0;
                latt[xp1][yp1][zp] = 0;
                latt[xp][yp1][zp1] = 0;
                latt[xp1][yp1][zp1] = 0;
                return true;
			}
			else
				return true;
		}
        break;
		
	    case 3:
        {// jump in +z direction
            zp2 = ipz2[zp];

            testlat = latt[xp][yp][zp2] + latt[xp1][yp][zp2] + latt[xp][yp1][zp2] + latt[xp1][yp1][zp2];

            if(testlat==0)
		    {
                monlatp[mono][3] = zp1;
                
                latt[xp][yp][zp2] = mono;
                latt[xp1][yp][zp2] = mono;
                latt[xp][yp1][zp2] = mono;
                latt[xp1][yp1][zp2] = mono;
                latt[xp][yp][zp] = 0;
                latt[xp1][yp][zp] = 0;
                latt[xp][yp1][zp] = 0;
                latt[xp1][yp1][zp] = 0;
                return true;
		    }
		    else
			    return true;
        }
        break;
        case 4 :
        {// jump in -z direction
            zm1 = imz[zp];

            testlat =  latt[xp][yp][zm1] + latt[xp1][yp][zm1] + latt[xp][yp1][zm1] + latt[xp1][yp1][zm1];

            if(testlat==0)
		    {
                monlatp[mono][3] = zm1;
                
                latt[xp][yp][zm1] = mono;
                latt[xp1][yp][zm1] = mono;
                latt[xp][yp1][zm1] = mono;
                latt[xp1][yp1][zm1] = mono;
                latt[xp][yp][zp1] = 0;
                latt[xp1][yp][zp1] = 0;
                latt[xp][yp1][zp1] = 0;
                latt[xp1][yp1][zp1] = 0;
                return true;
		    }
		    else
                return true;
		}
        break;
    }
    return true;
}

int ffxyz()
{  
    int i;

// These are the arrays for the periodic boundary conditions.
//*********************x***********************************
    for(i=1;i<=lsx;i++)
    {
        ipx[i] = i+1;
        ipx2[i] = i+2;
        imx[i] = i-1;
    }
    ipx[lsx] = 1;
    ipx2[lsx-1] = 1;
    ipx2[lsx] = 2;
    imx[1] = lsx;
//********************y************************************
    for(i=1;i<=lsy;i++)
    {
        ipy[i] = i+1;
        ipy2[i] = i+2;
        imy[i] = i-1;
    }
    ipy[lsy] = 1;
    ipy2[lsy-1] = 1;
    ipy2[lsy] = 2;
    imy[1] = lsy;
//********************z************************************
    for(i=1;i<=lsz;i++)
    {
        ipz[i] = i+1;
        ipz2[i] = i+2;
        imz[i] = i-1;
    }
    ipz[lsz] = 1;
    ipz2[lsz-1] = 1;
    ipz2[lsz] = 2;
    imz[1] = lsz;

    return 0;
}

int outPDB()
{//Stores the final configuration of the simulation into a PDB format file

    int i,j;
    char bbf[100];
    FILE* fp;

    sprintf(bbf,"initial.pdb");
    if((fp=fopen( bbf, "w+" )) == NULL)
        printf( "The file was not opened\n" );
    else
    {
        fprintf(fp,"TITLE     DI-VINYL SYSTEM\n");
        fprintf(fp,"REMARK    SHOW IN SIMULATION BOX\n");
        fprintf(fp,"CRYST1%9.3f%9.3f%9.3f%7.2f%7.2f%7.2f P 1\n",lsx*1.0,lsy*1.0,lsz*1.0,90.0,90.0,90.0);

        for( i=1; i<=ntot; i++)
        {
            if(i<=nactiR)	
            {
                fprintf(fp,"%4s%7d  %4s%4s %4d%1s   %8.3f%8.3f%8.3f%6.2f%6.2f\n",
                        "ATOM",i,"SSS","act",1," ",float(monlatp[i][1]),float(monlatp[i][2]),float(monlatp[i][3]),0.0,0.0);
            }
            else if(i>nactiR&&i<=ndormR)
			{
                fprintf(fp,"%4s%7d  %4s%4s %4d%1s   %8.3f%8.3f%8.3f%6.2f%6.2f\n",
                        "ATOM",i,"SSS","dor",1," ",float(monlatp[i][1]),float(monlatp[i][2]),float(monlatp[i][3]),0.0,0.0);
            }
			else
            {
                fprintf(fp,"%4s%7d  %4s%4s %4d%1s   %8.3f%8.3f%8.3f%6.2f%6.2f\n",
                        "ATOM",i,"SSS","MON",1," ",float(monlatp[i][1]),float(monlatp[i][2]),float(monlatp[i][3]),0.0,0.0);
            }
        }

        fprintf(fp, "END\n");
        fclose(fp);
    }
    return 0;
}

int main()
{
    int i, j;

    srand( (unsigned)time( NULL ) );

    unsigned long initseed[4], length=4;

    initseed[0]=rand()%9000;
    initseed[1]=rand()%9000;
    initseed[2]=rand()%9000;
    initseed[3]=rand()%9000;

    init_by_array(initseed, length);
	
    ffxyz();

    mcs=1;

    ini();
	 	 
    for(i=mcs;i<=MCS;i++)
    {
        for(j=1;j<=ntot;j++)
        {
            mono = genrand_int32()%ntot+1;
            movement();
        }
        printf("mcs=%ld\n",i);
    }

    outPDB();
    bflout(i);

    printf("Initialzation is finished.\n");
    return 0;
}

