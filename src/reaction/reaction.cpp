/*
Copyright (C) 2017 Zidan Zhang <zidan.zhang@kuleuven.be>
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

//This program is used for reaction for di-vinyl Controlled Chain Growth project

#include "math.h"
#include "stdio.h"
#include "stdlib.h"
#include "time.h"

#include <iostream>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>    

#define nmon      150480                   // Number of monomers
#define nrchain   1520                     // Number of chains (active radical + dormant radical chains)
#define nactiR    1                         // Number of active radicals
#define ndormR    1519                     // Number of dormant radicals
#define ntot      (nmon+nrchain)            // Total number of particles           
#define lsx       200                       
#define lsy       200
#define lsz       200       

int ipx[lsx+1],ipx2[lsx+1],imx[lsx+1];        // ipx, ipx2, imx are the x positions of mono opposite particle, positive move of mono and the negative move of mono.
int ipy[lsy+1],ipy2[lsy+1],imy[lsy+1];
int ipz[lsz+1],ipz2[lsz+1],imz[lsz+1];
int monlatp[ntot+1][3+1],montype[ntot+1];     // coordinate of a site of every particle    
int monlinks[ntot+1][4+1],monbd[ntot+1][4+1]; // mono1 2 3 4 which linked with mono; type of bonds which formed with mono
int numbonds[ntot+1],monreactive[ntot+1];     // how many bonds are formed with every particle
int latt[lsx+1][lsy+1][lsz+1];                // latt number of every site in the lattice (sol is 0, particle is 1 2...)

int bonds[109+1][3+1],ffbd[54+1];
int ffx[lsx+1][54+1],ffy[lsy+1][54+1],ffz[lsz+1][54+1];
int ffx1[lsx+1][54+1],ffy1[lsy+1][54+1],ffz1[lsz+1][54+1];
int move[109+1][6+1];
int chain_premark[ntot+1];
int mono,mono1,nu1;

int radi_mon,radi_Pinter,radi_Pintra;
int chain1,topchainlength;                 
int act,Xm;

double Pw,Pn,PDI,RDP,intraratio,Cm,Cv,Cp;          

int chainlength[nrchain+1],chainlength1[nrchain+1],pendent[nrchain+1],dormpos[ndormR+1];
int unique[nrchain+1],numunique[nrchain+1];

////////////////////////random generator///////////////////////  
#define NNNN 624           
#define MMMM 397
#define MATRIX_A 0x9908b0dfUL   
#define UMASK 0x80000000UL 
#define LMASK 0x7fffffffUL 
#define MIXBITS(u,v) ( ((u) & UMASK) | ((v) & LMASK) )
#define TWIST(u,v) ((MIXBITS(u,v) >> 1) ^ ((v)&1UL ? MATRIX_A : 0UL))

static unsigned long randstate[NNNN]; 
static int randleft = 1;
static int randinitf = 0;
static unsigned long *randnext;

/* initializes randstate[NNNN] with a seed */
void init_genrand(unsigned long s)
{
    int j;
    randstate[0]= s & 0xffffffffUL;
    for (j=1; j<NNNN; j++) 
	{
        randstate[j] = (1812433253UL * (randstate[j-1] ^ (randstate[j-1] >> 30)) + j);
        randstate[j] &= 0xffffffffUL;  /* for >32 bit machines */
    }
    randleft = 1; randinitf = 1;
}

/* initialize by an array with array-length */
void init_by_array(unsigned long init_key[], unsigned long key_length)
{
    int i, j, k;
    init_genrand(19650218UL);
    i=1; j=0;
    k = (NNNN>key_length ? NNNN : key_length);
	
    for (; k; k--) 
	{
        randstate[i] = (randstate[i] ^ ((randstate[i-1] ^ (randstate[i-1] >> 30)) * 1664525UL)) + init_key[j] + j;
        randstate[i] &= 0xffffffffUL; 
        i++; j++;
        if (i>=NNNN) 
		{ 
	        randstate[0] = randstate[NNNN-1]; 
		    i=1; 
	    }
        if (j>=key_length) 
			j=0;
    }
	
    for (k=NNNN-1; k; k--) 
	{
        randstate[i] = (randstate[i] ^ ((randstate[i-1] ^ (randstate[i-1] >> 30)) * 1566083941UL)) - i; 
        randstate[i] &= 0xffffffffUL; 
        i++;
        if (i>=NNNN) 
		{ 
	        randstate[0] = randstate[NNNN-1];
			i=1; 
		}
    }

    randstate[0] = 0x80000000UL; 
    randleft = 1; 
	randinitf = 1;
}

static void randnext_state(void)
{
    unsigned long *p=randstate;
    int j;

    if (randinitf==0) 
		init_genrand(5489UL);
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

    if (--randleft == 0) 
		randnext_state();
        y = *randnext++;
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

    if (--randleft == 0) 
		randnext_state();
        y = *randnext++;
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

    if (--randleft == 0) 
		randnext_state();
        y = *randnext++;
        y ^= (y >> 11);
        y ^= (y << 7) & 0x9d2c5680UL;
        y ^= (y << 15) & 0xefc60000UL;
        y ^= (y >> 18);
    return (double)y * (1.0/4294967295.0);
}

/* generates a random number on [0,1)-real-interval */
double genrand_real2(void)
{
    unsigned long y;

    if (--randleft == 0) 
		randnext_state();
        y = *randnext++;
        y ^= (y >> 11);
        y ^= (y << 7) & 0x9d2c5680UL;
        y ^= (y << 15) & 0xefc60000UL;
        y ^= (y >> 18);
    return (double)y * (1.0/4294967296.0);
}

/* generates a random number on (0,1)-real-interval */
double genrand_real3(void)
{
    unsigned long y;

    if (--randleft == 0) 
		randnext_state();
        y = *randnext++;
        y ^= (y >> 11);
        y ^= (y << 7) & 0x9d2c5680UL;
        y ^= (y << 15) & 0xefc60000UL;
        y ^= (y >> 18);
    return ((double)y + 0.5) * (1.0/4294967296.0);
}

/* generates a random number on [0,1) with 53-bit resolution*/
double genrand_res53(void)
{
    unsigned long a=genrand_int32()>>5, b=genrand_int32()>>6;
    return(a*67108864.0+b)*(1.0/9007199254740992.0);
}
////////////////////////random generator///////////////////////  

////////all main program//////////////

int  bdibfl()
{
    int max, ipegel, i, j, k, index, ind;
    int startvec[6+1][3+1], zielvec[50+1][3+1];
    int dumvec[50+1][3+1], dummy;
	
    bool test;

    startvec[1][1] = 2;
    startvec[1][2] = 0;
    startvec[1][3] = 0;

    startvec[2][1] = 2;
    startvec[2][2] = 1;
    startvec[2][3] = 0;

    startvec[3][1] = 2;
    startvec[3][2] = 1;
    startvec[3][3] = 1;

    startvec[4][1] = 2;
    startvec[4][2] = 2;
    startvec[4][3] = 1;

    startvec[5][1] = 3;
    startvec[5][2] = 0;
    startvec[5][3] = 0;

    startvec[6][1] = 3;
    startvec[6][2] = 1;
    startvec[6][3] = 0;

    max = 0;
	
    for(i=1;i<=6;i++)
    {
        ind = 1;
        for(j=1;j<=2;j++)
        {
            for(k=1;k<=3;k++)
            {
                zielvec[ind][1] = startvec[i][1];
                zielvec[ind][2] = startvec[i][2];
                zielvec[ind][3] = startvec[i][3];
                ind = ind + 1;
                zielvec[ind][1] = startvec[i][1];
                zielvec[ind][2] = startvec[i][2];
                zielvec[ind][3] = - startvec[i][3];
                ind = ind + 1;
                zielvec[ind][1] = startvec[i][1];
                zielvec[ind][2] = - startvec[i][2];
                zielvec[ind][3] = startvec[i][3];
                ind = ind + 1;
                zielvec[ind][1] = startvec[i][1];
                zielvec[ind][2] = - startvec[i][2];
                zielvec[ind][3] = - startvec[i][3];
                ind = ind + 1;
                zielvec[ind][1] = - startvec[i][1];
                zielvec[ind][2] = startvec[i][2];
                zielvec[ind][3] = startvec[i][3];
                ind = ind + 1;
                zielvec[ind][1] = - startvec[i][1];
                zielvec[ind][2] = startvec[i][2];
                zielvec[ind][3] = - startvec[i][3];
                ind = ind + 1;
                zielvec[ind][1] = - startvec[i][1];
                zielvec[ind][2] = - startvec[i][2];
                zielvec[ind][3] = startvec[i][3];
                ind = ind + 1;
                zielvec[ind][1] = - startvec[i][1];
                zielvec[ind][2] = - startvec[i][2];
                zielvec[ind][3] = - startvec[i][3];
                ind = ind + 1;
                dummy = startvec[i][1];
                startvec[i][1] = startvec[i][2];
                startvec[i][2] = startvec[i][3];
                startvec[i][3] = dummy;
            }
			
            dummy = startvec[i][1];
            startvec[i][1] = startvec[i][2];               
            startvec[i][2] = dummy;
        }

        dumvec[1][1] = zielvec[1][1];
        dumvec[1][2] = zielvec[1][2];
        dumvec[1][3] = zielvec[1][3];
        ipegel = 2;

        for (k=1;k<=48;k++)
        {
            index = 1;
            test =false;
			
            UU333: if((!test)&&(index<ipegel))                       
            {
                test = ((zielvec[k][1]==dumvec[index][1])&&(zielvec[k][2]==dumvec[index][2])&&(zielvec[k][3]==dumvec[index][3]));
                index = index + 1;
                goto UU333;
            }

            if(!test)
            {
                dumvec[ipegel][1] = zielvec[k][1];             
                dumvec[ipegel][2] = zielvec[k][2];
                dumvec[ipegel][3] = zielvec[k][3];
                ipegel = ipegel + 1;
            }
        }

        for(j=1;j<=ipegel-1;j++)
        {
            bonds[max+j][1] = dumvec[j][1];
            bonds[max+j][2] = dumvec[j][2];
            bonds[max+j][3] = dumvec[j][3];
        }
        max = max + ipegel - 1;

    }
	
    return 0;
}

bool iniflin()
{
    int i,j,k;
    int tdu1,tdu2,tdu3,tdu4;

    FILE* fp;

    montype[0]=0;
    numbonds[0]=0;
    monreactive[0]=0;

    if((fp=fopen("ini.dat", "r" )) == NULL)
    {
        return false;
    }
    else
    {
        fscanf(fp,"%ld %ld %ld %ld\n", &tdu1,&tdu2,&tdu3,&tdu4);
        printf("%ld %ld %ld %ld\n", &tdu1,&tdu2,&tdu3,&tdu4);
		
        for(i=1;i<=ntot;i++)
        {
            fscanf(fp,"%ld %ld %ld\n", monlatp[i][1],monlatp[i][2],monlatp[i][3]);
            fscanf(fp,"%ld %ld %ld %ld %ld %ld %ld %ld\n", monlinks[i][1],monlinks[i][2],monlinks[i][3],monlinks[i][4],monbd[i][1],monbd[i][2],monbd[i][3],monbd[i][4]);
            fscanf(fp,"%ld %ld %ld\n",montype[i],numbonds[i],monreactive[i]);
        }

        fclose(fp);
    }

    int xp,yp,zp,xp1,yp1,zp1;

    for(i=1;i<=lsx;i++)
        for(j=1;j<=lsy;j++)
            for(k=1;k<=lsz;k++)
                latt[i][j][k]=0;

    for(i=1;i<=ntot;i++)   
    {
        xp=monlatp[i][1];	
		yp=monlatp[i][2];	
		zp=monlatp[i][3];  
		xp1=ipx[xp];	
		yp1=ipy[yp];	
		zp1=ipz[zp];
        latt[xp][yp][zp]=i;
        latt[xp1][yp][zp]=i;
        latt[xp][yp1][zp]=i;
        latt[xp][yp][zp1]=i;
        latt[xp1][yp1][zp]=i;
        latt[xp1][yp][zp1]=i;
        latt[xp][yp1][zp1]=i;
        latt[xp1][yp1][zp1]=i;
    }

    return true;
}

bool movement()
{
    int dir, xp, yp, zp;
    int xm1, xp1, xp2, ym1, yp1, yp2, zm1, zp1, zp2;
    int testlat;
    int i,i1,newbd[4];

    dir = genrand_int32()%6 + 1;

    for(i=1;i<=numbonds[mono];i++)
    {
        newbd[i]=move[monbd[mono][i]][dir]; // whether the movement is accepted by bond length.                   
        if(newbd[i]==0) 
		   return true;
    }
	
    xp = monlatp[mono][1];
    yp = monlatp[mono][2];
    zp = monlatp[mono][3];
    xp1 = ipx[xp];
    yp1 = ipy[yp];
    zp1 = ipz[zp];

    switch( dir )
    {
        case 1:
        {
            xp2 = ipx2[xp];
            testlat = latt[xp2][yp][zp] + latt[xp2][yp1][zp] + latt[xp2][yp][zp1] + latt[xp2][yp1][zp1];
            if(testlat==0)
            {
                monlatp[mono][1] = xp1;

                for(i=1;i<=numbonds[mono];i++)
                {
                    mono1=monlinks[mono][i];
					
                    for(i1=1;i1<=numbonds[mono1];i1++)
                    {
                        if(monbd[mono][i]==(109-monbd[mono1][i1]))
                        {
							monbd[mono1][i1]=109-newbd[i];
					        break;
						}
                    }
                    monbd[mono][i]=newbd[i];
                }

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
        {
            xm1 = imx[xp];
            testlat = latt[xm1][yp][zp] + latt[xm1][yp1][zp] + latt[xm1][yp][zp1] + latt[xm1][yp1][zp1];

            if(testlat==0)
            {
                monlatp[mono][1] = xm1;

                for(i=1;i<=numbonds[mono];i++)
                {
                    mono1=monlinks[mono][i];
					
                    for(i1=1;i1<=numbonds[mono1];i1++)
                    {
                        if(monbd[mono][i]==(109-monbd[mono1][i1]))
                        {
							monbd[mono1][i1]=109-newbd[i];
							break;
						}
                    }
                    monbd[mono][i]=newbd[i];
                }

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
        {
            yp2 = ipy2[yp];
            testlat = latt[xp][yp2][zp] + latt[xp1][yp2][zp] + latt[xp][yp2][zp1] + latt[xp1][yp2][zp1];
            if(testlat==0)
            {
                monlatp[mono][2] = yp1;

                for(i=1;i<=numbonds[mono];i++)
                {
                    mono1=monlinks[mono][i];
					
                    for(i1=1;i1<=numbonds[mono1];i1++)
                    {
                        if(monbd[mono][i]==(109-monbd[mono1][i1]))
                        {
							monbd[mono1][i1]=109-newbd[i];
							break;
						}
                    }
                    monbd[mono][i]=newbd[i];
                }
				
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
        {
            ym1 = imy[yp];
            testlat= latt[xp][ym1][zp] + latt[xp1][ym1][zp] + latt[xp][ym1][zp1] + latt[xp1][ym1][zp1];
			
            if(testlat==0)
            {
                monlatp[mono][2] = ym1;

                for(i=1;i<=numbonds[mono];i++)
                {
                    mono1=monlinks[mono][i];
					
                    for(i1=1;i1<=numbonds[mono1];i1++)
                    {
                        if(monbd[mono][i]==(109-monbd[mono1][i1]))
                        {
							monbd[mono1][i1]=109-newbd[i];
							break;
						}
                    }
                    monbd[mono][i]=newbd[i];
                }
				
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
        {
            zp2 = ipz2[zp];
            testlat = latt[xp][yp][zp2] + latt[xp1][yp][zp2] + latt[xp][yp1][zp2] + latt[xp1][yp1][zp2];
			
            if(testlat==0)
            {
                monlatp[mono][3] = zp1;

                for(i=1;i<=numbonds[mono];i++)
                {
                    mono1=monlinks[mono][i];
					
                    for(i1=1;i1<=numbonds[mono1];i1++)
                    {
                        if(monbd[mono][i]==(109-monbd[mono1][i1]))
                        {
							monbd[mono1][i1]=109-newbd[i];
							break;
						}
                    }
                    monbd[mono][i]=newbd[i];
                }

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
        {
            zm1 = imz[zp];
            testlat =  latt[xp][yp][zm1] + latt[xp1][yp][zm1] + latt[xp][yp1][zm1] + latt[xp1][yp1][zm1];
			
            if(testlat==0)
            {
                monlatp[mono][3] = zm1;

                for(i=1;i<=numbonds[mono];i++)
                {
                    mono1=monlinks[mono][i];
					
                    for(i1=1;i1<=numbonds[mono1];i1++)
                    {
                        if(monbd[mono][i]==(109-monbd[mono1][i1]))
                        {
							monbd[mono1][i1]=109-newbd[i];
							break;
						}
                    }
                    monbd[mono][i]=newbd[i];
                }

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
    int i,j,k,i1,j1,k1,tx,ty,tz,tx1,ty1,tz1;
    int n1,tl2;

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

/////////////////////54 positions around a unit/////////
    for(i=1;i<=lsx;i++)                                
    {                                                    
        n1=0;
		
        for(i1=-2;i1<=2;i1++)
            for(j1=-2;j1<=2;j1++)
                for(k1=-2;k1<=2;k1++)
                {
                    tx=i+i1;
                    tx1=i+1+i1;
                    tl2=i1*i1+j1*j1+k1*k1;
					
                    if((tl2>=4)&&(tl2<=6))
                    {
                        n1++;
						
                        if(tx<=0) 
						    tx=tx+lsx; 
					    if(tx>lsx) 
						    tx=tx-lsx;
                        if(tx1<=0) 
						    tx1=tx1+lsx; 
					    if(tx1>lsx) 
						    tx1=tx1-lsx;
					   
                        ffx[i][n1]=tx; 
						ffx1[i][n1]=tx1;
                    }
                }
    }

    for(j=1;j<=lsy;j++)
    {
        n1=0;
        for(i1=-2;i1<=2;i1++)
            for(j1=-2;j1<=2;j1++)
                for(k1=-2;k1<=2;k1++)
                {
                    ty=j+j1;
                    ty1=j+1+j1;
                    tl2=i1*i1+j1*j1+k1*k1;
					
                    if((tl2>=4)&&(tl2<=6))
                    {
                        n1++;
                        if(ty<=0) 
							ty=ty+lsy; 
						if(ty>lsy) 
							ty=ty-lsy;
                        if(ty1<=0) 
							ty1=ty1+lsy; 
						if(ty1>lsy) 
							ty1=ty1-lsy;
						
                        ffy[j][n1]=ty; 
						ffy1[j][n1]=ty1;
                    }
                }
    }

    for(k=1;k<=lsz;k++)
    {
        n1=0;
        for(i1=-2;i1<=2;i1++)
            for(j1=-2;j1<=2;j1++)
                for(k1=-2;k1<=2;k1++)
                {
                    tz=k+k1;
                    tz1=k+1+k1;
                    tl2=i1*i1+j1*j1+k1*k1;
					
                    if((tl2>=4)&&(tl2<=6))
                    {
                        n1++;
						
                        if(tz<=0) 
							tz=tz+lsz; 
						if(tz>lsz) 
							tz=tz-lsz;
                        if(tz1<=0) 
							tz1=tz1+lsz; 
						if(tz1>lsz) 
							tz1=tz1-lsz;
						
                        ffz[k][n1]=tz; 
						ffz1[k][n1]=tz1;
                    }
                }
    }
	
////////////////////////the type of bonds as for the 54 positions//////////////////////////
    n1=0;
	
    for(i1=-2;i1<=2;i1++)
        for(j1=-2;j1<=2;j1++)
            for(k1=-2;k1<=2;k1++)
            {
                tl2=i1*i1+j1*j1+k1*k1;
				
                if((tl2>=4)&&(tl2<=6))
                {
                    n1++;
                    tx=-i1;
					ty=-j1;
					tz=-k1;
					
                    for(i=1;i<=108;i++)
                    {
                        if(tx==bonds[i][1])
                        if(ty==bonds[i][2])
                        if(tz==bonds[i][3])
                            ffbd[n1]=i;                   
                    }
                }
            }		
  return 0;
}

/////////requeue all bonds with the relation n1=109-n2 which are contrary in directions /////////
int iniffxyz()
{
    int i,j,bondst[4];
   
    for(i=1;i<=54;i++)
        for(j=1;j<=108;j++)
        {
            if(bonds[i][1]==(-bonds[j][1]))
            if(bonds[i][2]==(-bonds[j][2]))
            if(bonds[i][3]==(-bonds[j][3]))
            {
                bondst[1]=bonds[j][1];
                bondst[2]=bonds[j][2];
                bondst[3]=bonds[j][3];

                bonds[j][1]=bonds[109-i][1];
                bonds[j][2]=bonds[109-i][2];
                bonds[j][3]=bonds[109-i][3];

                bonds[109-i][1]=bondst[1];
                bonds[109-i][2]=bondst[2];
                bonds[109-i][3]=bondst[3];
            }
        }
    return 0;
}

int inimove()
{
    int i, j, k, neww[6+1][3+1];
	
    bool test;

    for(i=1;i<=108;i++)
    {
        neww[1][1] = bonds[i][1] + 1;
        neww[1][2] = bonds[i][2];
        neww[1][3] = bonds[i][3];
        neww[2][1] = bonds[i][1];
        neww[2][2] = bonds[i][2] + 1;
        neww[2][3] = bonds[i][3];
        neww[3][1] = bonds[i][1];
        neww[3][2] = bonds[i][2];
        neww[3][3] = bonds[i][3] + 1;
        neww[4][1] = bonds[i][1];
        neww[4][2] = bonds[i][2];
        neww[4][3] = bonds[i][3] - 1;
        neww[5][1] = bonds[i][1];
        neww[5][2] = bonds[i][2] - 1;
        neww[5][3] = bonds[i][3];
        neww[6][1] = bonds[i][1] - 1;
        neww[6][2] = bonds[i][2];
        neww[6][3] = bonds[i][3];

        for(j=1;j<=6;j++)
        {
            test = false;
            move[i][j]=0;
			
            for(k=1;k<=108;k++)
            {
                test = ((neww[j][1]==bonds[k][1])&&(neww[j][2]==bonds[k][2]))&&(neww[j][3]==bonds[k][3]);
                if (test) 
					move[i][j]= k;
            }
        }
    }

    for(i=1;i<=6;i++) 
		move[109][i] = 109;

    return 0;
}

int inilp()  // initialize chainlength and pendent number of each chain
{
	int i;
	
	for(i=1;i<=nrchain;i++)
	{	
        chainlength[i]=1;
		chainlength1[i]=1;
	    pendent[i]=1;
	}
	return 0;
}

int inidorp()  //initialize latt number of each dormant radical
{
	int i,j;
	j=1;
	
	for(i=1;i<=ntot;i++)
	{
		if(montype[i]==0)
		{
			dormpos[j]=i;
		    j++;
		}
	}
	return 0;	
}	

int inichain()    // the number of chains in the system is constant, every radical is a chain precursor
{
  int i;
  chain1=1;
  
  for(i=1;i<=ntot;i++)
  {
    if(montype[i]!=2)
	{
        chain_premark[i]=chain1;
        chain1++;	
	}
    else	
	{		
        chain_premark[i]=0;
	}
  }
  return 0;
}

int mark12(int i,int chain1)   // no distinguish of primary and secondary chain
{
    int j;

    for(j=1;j<=numbonds[i];j++)
    {
        if(chain_premark[monlinks[i][j]]!=chain1)
        {
            chain_premark[monlinks[i][j]]=chain1;
            mark12(monlinks[i][j],chain1);
        }
    }
    return 0;
}

int reaction()
{
    int in,nu2,dir;              
    int xxx,yyy,zzz,marktmp;
    int channelbd;                                      
 
	    xxx=monlatp[act][1];  // input the active radical number-act, and find its coordinate
        yyy=monlatp[act][2];
        zzz=monlatp[act][3];
	
        marktmp=chain_premark[act]; // the chain number of act
	
            in=genrand_int32()%54+1; // select the mono to react with
            nu1=latt[ffx[xxx][in]][ffy[yyy][in]][ffz[zzz][in]];
            nu2=latt[ffx1[xxx][in]][ffy1[yyy][in]][ffz1[zzz][in]];
			
			while((nu1!=nu2)||(monreactive[nu1]==0)) //only when nu1=nu2 and have reactive site, reaction can occur
			{	
		            in=genrand_int32()%54+1;
                    nu1=latt[ffx[xxx][in]][ffy[yyy][in]][ffz[zzz][in]];
                    nu2=latt[ffx1[xxx][in]][ffy1[yyy][in]][ffz1[zzz][in]];      
			}	
			
            if(monreactive[nu1]==4) //linear addition
            {
					radi_mon++;         // linear propagation times
					
					monreactive[act]--; monreactive[nu1]=2; //the radical site turns to bond; monomer forms a bond and turns to dormant radical
					
					if (monreactive[act]==2)
					{   
				        montype[act]=3; // pendent vinyl formed, not radical
					}
					else
					{
						montype[act]=4; // fully reacted crosslinker formed, no active site
                    }
					
				    chainlength[marktmp]++;
					chainlength1[marktmp]++;
					pendent[marktmp]++;
					Xm--;
					
					montype[nu1]=0; //monomer turns to a dormant radical
					
					channelbd=ffbd[in]; // the bond type of connection towards this position(one of 54 positions)
					numbonds[act]++; numbonds[nu1]++; //radical and monomer both formed one new bond
					monbd[act][numbonds[act]]=channelbd; // new bond type
                    monbd[nu1][numbonds[nu1]]=109-channelbd;
					monlinks[act][numbonds[act]]=nu1;// record which bead connected with act
                    monlinks[nu1][numbonds[nu1]]=act;
					mark12(act,marktmp); //the new reacted monomer is marked to marktemp
			}
			else //inter or intra	
			{
				    if(chain_premark[nu1]!=marktmp)
					{   
				        radi_Pinter++;         // inter-crosslinking times
					
					    monreactive[act]--; monreactive[nu1]=0; //the radical site turns to bond; pendent vinyl turns to a bond and a dormant radical
					
					    if(monreactive[act]==2)
					    {   
				           montype[act]=3; // pendent vinyl formed, not radical
						}
					    else
						{
						   montype[act]=4; // fully reacted crosslinker formed, no active site
                        }
					
						chainlength[marktmp]=chainlength[marktmp]+chainlength[chain_premark[nu1]]; //two chains combined to one
						pendent[marktmp]=pendent[marktmp]+pendent[chain_premark[nu1]]-1; //update the amount of pendent vinyls in marktmp
						chainlength[chain_premark[nu1]]=0; //remove the record for chain nu1
						pendent[chain_premark[nu1]]=0;  
						
						montype[nu1]=0; //monomer turns to a dormant radical
					
					    channelbd=ffbd[in]; // the bond type of connection towards this position(one of 54 positions)
					    numbonds[act]++; numbonds[nu1]++; //radical and monomer both formed one new bond
					    monbd[act][numbonds[act]]=channelbd; // new bond type
                        monbd[nu1][numbonds[nu1]]=109-channelbd;
					    monlinks[act][numbonds[act]]=nu1;// record which bead connected with act
                        monlinks[nu1][numbonds[nu1]]=act;
						mark12(act,marktmp);     // two chain numbers become same
					}
			        else 
					{
						radi_Pintra++;         // intra-crosslinking times
						monreactive[act]--; monreactive[nu1]=0; //the radical site turns to bond; pendent vinyl turns to a bond and a dormant radical
					
					    if(monreactive[act]==2)
					    {   
				           montype[act]=3; // pendent vinyl formed, not radical
						}
					    else
						{
						   montype[act]=4; // fully reacted crosslinker formed, no active site
                        }
						
						pendent[marktmp]--;
						montype[nu1]=0; //monomer turns to a dormant radical
					
					    channelbd=ffbd[in]; // the bond type of connection towards this position(one of 54 positions)
					    numbonds[act]++; numbonds[nu1]++; //radical and monomer both formed one new bond
					    monbd[act][numbonds[act]]=channelbd; // new bond type
                        monbd[nu1][numbonds[nu1]]=109-channelbd;
					    monlinks[act][numbonds[act]]=nu1;// record which bead connected with act
                        monlinks[nu1][numbonds[nu1]]=act;
					}
			} 
				
    return 0;
}

int equilibrium()  // after each reaction, activate a new radical and store the dormant radical
{
	int dor;
	
	dor=genrand_int32()%1519+1;
	act=dormpos[dor];
	dormpos[dor]=nu1;
	monreactive[act]=monreactive[act]+1;
	montype[act]=1;
	
	return 0;
}

///////////////////////////analysis////////////////////////
int analysis()
{
    int i,j,k,numchain;
    int sum,sump,sPw;
    int test,i1;
	
    numchain=0;
	sum=0;
	sump=0;
	
	for(i=1;i<=nrchain;i++) // the number of total pendent vinyls, the totoal DP, the number of chains
    {
        sump=sump+pendent[i];
		sum=sum+chainlength[i];
		
		if(chainlength[i]!=0)
		{ 
	      numchain++;
		}
		
    }
		
    topchainlength=0;
	
    for(i=1;i<=nrchain;i++) // the biggest chain
    {      
        if(chainlength[i]>topchainlength)
        {
			topchainlength=chainlength[i];
		}
    }

	k=0;
	for(i=1;i<=nrchain;i++)
	{
		if(chainlength[i]!=0)
		{
			test=1;
		    j=1;
			while(test!=0&j<i)
			{
				test=chainlength[i]-chainlength[j];
				if(test==0)  // this chainlength has already been stored in unique,find it and increase the number of it 
				{
					for(i1=1;i1<=k;i1++)
					{
						if(unique[i1]==chainlength[i])
							numunique[i1]++;
					}
				}
				else
				{
					j++;
				}
			}
			if((test!=0)&&(j=i)) //a unique chainlength was found, store it in unique and initialize its number
			{
				k++;
				unique[k]=chainlength[i];
				numunique[k]=1;
			}
		}
	}
	
    sPw=0;
	
    for(i=1;i<=k;i++)
    {
        sPw=sPw+unique[i]*unique[i]*numunique[i];      
    }
	
    Pw=(sPw*1.0)/sum;
    Pn=sum/(numchain*1.0);
    PDI=Pw/Pn;
    RDP=((sPw-topchainlength*topchainlength)*1.0)/(sum-topchainlength);
	intraratio=(radi_Pintra*1.0)/(radi_Pinter+radi_Pintra);
	
    Cv=Cm-sump/(2.0*152000);
	Cp=(2.0*Cv-Cm)/Cm;
	
    return 0;
}
/////////////////analysis//////////////////////////////

int bflout2()   //output the final results
{
    FILE* fp;

    if((fp=fopen( "result_1.dat", "a+" )) == NULL)
        printf( "The file was not opened\n" );
    else
    {
        fprintf(fp,"%lf %lf %lf %lf %lf %lf %lf %lf\n",Cm,Pn,Pw,PDI,RDP,Cv,Cp,intraratio);
        fclose(fp);
    }

    return 0;
}

int main()
{
    int iii,iii1,i,j;
	double CS; 
	
    srand((unsigned)time(NULL));
    unsigned long initseed[4], length=4;
	
    initseed[0]=rand()%9000;
	initseed[1]=rand()%9000;
	initseed[2]=rand()%9000;
	initseed[3]=rand()%9000;

    init_by_array(initseed, length);

    bdibfl();
     
	iniffxyz();

    inimove();
	
	ffxyz();
	
	inilp();
	
	inidorp();
	
	inichain();

    act=1; 
	Xm=nmon;
	    
	radi_Pinter=0;
	radi_Pintra=0;
	radi_mon=0;
	
	CS=0.0008;
	
	Cm=0.01;
	
	FILE* fp;
    char bbf[100];

    sprintf(bbf,"result_%ld.dat",Cm);

    if((fp=fopen( bbf, "a+" )) == NULL)
        printf( "The file was not opened\n" );
    else
    {
        fprintf(fp,"Cm  Pn  Pw  PDI  RDP  Cv  Cp  intraratio\n");
        fclose(fp);
    }
	
	if(!iniflin())  //import the initial configuration, if error, end 
			return 1;
	
	while(Cm<=0.8) // successfully imported initial configuration
	{
        reaction(); 
		equilibrium();
		
		for(i=1;i<=638;i++)
		{	
		    for(j=1;j<=ntot;j++)
			{	
			  mono = genrand_int32()%ntot+ 1;
	          movement();
			}
		}
		
        Cm=(152000-Xm)*1.0/152000;   
	
	    if(Cm>=CS)     // record every 0.0008 divinyl monomer conversion
	    {
		   analysis();
		   bflout2();   
	       CS=CS+0.0008;
		   
		   printf("monomer conversion is%lf\n",Cm);
		
	    }
	}
	
    printf("Running is finished.\n");
	
    return 0;
}