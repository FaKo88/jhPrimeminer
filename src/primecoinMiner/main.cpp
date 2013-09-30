#include"global.h"

#include<intrin.h>
#include<ctime>
#include<map>
#include<conio.h>
#include<iostream>
#include<fstream>


primeStats_t primeStats = {0};
unsigned int nMaxSieveSize;
unsigned int nMaxPrimes;
bool nPrintDebugMessages;
bool nEnableAutoTune;
unsigned long nOverrideTargetValue;
unsigned int nOverrideBTTargetValue;
char* dt;

char* minerVersionString = "jhPrimeminer RdB v4 Beta";

bool error(const char *format, ...)
{
   puts(format);
   //__debugbreak();
   return false;
}


bool hex2bin(unsigned char *p, const char *hexstr, size_t len)
{
   bool ret = false;

   while (*hexstr && len) {
      char hex_byte[4];
      unsigned int v;

      if (!hexstr[1]) {
         printf("hex2bin str truncated");
         return ret;
      }

      memset(hex_byte, 0, 4);
      hex_byte[0] = hexstr[0];
      hex_byte[1] = hexstr[1];

      if (sscanf(hex_byte, "%x", &v) != 1) {
         printf( "hex2bin sscanf '%s' failed", hex_byte);
         return ret;
      }

      *p = (unsigned char) v;

      p++;
      hexstr += 2;
      len--;
   }

   if (len == 0 && *hexstr == 0)
      ret = true;
   return ret;
}



uint32 _swapEndianessU32(uint32 v)
{
   return ((v>>24)&0xFF)|((v>>8)&0xFF00)|((v<<8)&0xFF0000)|((v<<24)&0xFF000000);
}

uint32 _getHexDigitValue(uint8 c)
{
   if( c >= '0' && c <= '9' )
      return c-'0';
   else if( c >= 'a' && c <= 'f' )
      return c-'a'+10;
   else if( c >= 'A' && c <= 'F' )
      return c-'A'+10;
   return 0;
}

/*
* Parses a hex string
* Length should be a multiple of 2
*/
void yPoolWorkMgr_parseHexString(char* hexString, uint32 length, uint8* output)
{
   uint32 lengthBytes = length / 2;
   for(uint32 i=0; i<lengthBytes; i++)
   {
      // high digit
      uint32 d1 = _getHexDigitValue(hexString[i*2+0]);
      // low digit
      uint32 d2 = _getHexDigitValue(hexString[i*2+1]);
      // build byte
      output[i] = (uint8)((d1<<4)|(d2));	
   }
}

/*
* Parses a hex string and converts it to LittleEndian (or just opposite endianness)
* Length should be a multiple of 2
*/
void yPoolWorkMgr_parseHexStringLE(char* hexString, uint32 length, uint8* output)
{
   uint32 lengthBytes = length / 2;
   for(uint32 i=0; i<lengthBytes; i++)
   {
      // high digit
      uint32 d1 = _getHexDigitValue(hexString[i*2+0]);
      // low digit
      uint32 d2 = _getHexDigitValue(hexString[i*2+1]);
      // build byte
      output[lengthBytes-i-1] = (uint8)((d1<<4)|(d2));	
   }
}


void primecoinBlock_generateHeaderHash(primecoinBlock_t* primecoinBlock, uint8 hashOutput[32])
{
   uint8 blockHashDataInput[512];
   memcpy(blockHashDataInput, primecoinBlock, 80);
   sha256_context ctx;
   sha256_starts(&ctx);
   sha256_update(&ctx, (uint8*)blockHashDataInput, 80);
   sha256_finish(&ctx, hashOutput);
   sha256_starts(&ctx); // is this line needed?
   sha256_update(&ctx, hashOutput, 32);
   sha256_finish(&ctx, hashOutput);
}

void primecoinBlock_generateBlockHash(primecoinBlock_t* primecoinBlock, uint8 hashOutput[32])
{
   uint8 blockHashDataInput[512];
   memcpy(blockHashDataInput, primecoinBlock, 80);
   uint32 writeIndex = 80;
   sint32 lengthBN = 0;
   CBigNum bnPrimeChainMultiplier;
   bnPrimeChainMultiplier.SetHex(primecoinBlock->mpzPrimeChainMultiplier.get_str(16));
   std::vector<unsigned char> bnSerializeData = bnPrimeChainMultiplier.getvch();
   lengthBN = bnSerializeData.size();
   *(uint8*)(blockHashDataInput+writeIndex) = (uint8)lengthBN;
   writeIndex += 1;
   memcpy(blockHashDataInput+writeIndex, &bnSerializeData[0], lengthBN);
   writeIndex += lengthBN;
   sha256_context ctx;
   sha256_starts(&ctx);
   sha256_update(&ctx, (uint8*)blockHashDataInput, writeIndex);
   sha256_finish(&ctx, hashOutput);
   sha256_starts(&ctx); // is this line needed?
   sha256_update(&ctx, hashOutput, 32);
   sha256_finish(&ctx, hashOutput);
}

typedef struct  
{
   bool dataIsValid;
   uint8 data[128];
   uint32 dataHash; // used to detect work data changes
   uint8 serverData[32]; // contains data from the server 
}workDataEntry_t;

typedef struct  
{
   CRITICAL_SECTION cs;
   uint8 protocolMode;
   // xpm
   workDataEntry_t workEntry[128]; // work data for each thread (up to 128)
   // x.pushthrough
   xptClient_t* xptClient;
}workData_t;

#define MINER_PROTOCOL_GETWORK		(1)
#define MINER_PROTOCOL_STRATUM		(2)
#define MINER_PROTOCOL_XPUSHTHROUGH	(3)

workData_t workData;

jsonRequestTarget_t jsonRequestTarget; // rpc login data
jsonRequestTarget_t jsonLocalPrimeCoin; // rpc login data
bool useLocalPrimecoindForLongpoll;


/*
* Pushes the found block data to the server for giving us the $$$
* Uses getwork to push the block
* Returns true on success
* Note that the primecoin data can be larger due to the multiplier at the end, so we use 256 bytes per default
*/
bool jhMiner_pushShare_primecoin(uint8 data[256], primecoinBlock_t* primecoinBlock)
{
   if( workData.protocolMode == MINER_PROTOCOL_GETWORK )
   {
      // prepare buffer to send
      fStr_buffer4kb_t fStrBuffer_parameter;
      fStr_t* fStr_parameter = fStr_alloc(&fStrBuffer_parameter, FSTR_FORMAT_UTF8);
      fStr_append(fStr_parameter, "[\""); // \"]
      fStr_addHexString(fStr_parameter, data, 256);
      fStr_appendFormatted(fStr_parameter, "\",\"");
      fStr_addHexString(fStr_parameter, (uint8*)&primecoinBlock->serverData, 32);
      fStr_append(fStr_parameter, "\"]");
      // send request
      sint32 rpcErrorCode = 0;
      jsonObject_t* jsonReturnValue = jsonClient_request(&jsonRequestTarget, "getwork", fStr_parameter, &rpcErrorCode);
      if( jsonReturnValue == NULL )
      {
         printf("PushWorkResult failed :(\n");
         return false;
      }
      else
      {
         // rpc call worked, sooooo.. is the server happy with the result?
         jsonObject_t* jsonReturnValueBool = jsonObject_getParameter(jsonReturnValue, "result");
         if( jsonObject_isTrue(jsonReturnValueBool) )
         {
            primeStats.totalShares++;
            primeStats.validShares++;
            time_t now = time(0);
            dt = ctime(&now);
            //printf("Valid share found!");
            //printf("[ %d / %d ] %s",valid_shares, total_shares,dt);
            jsonObject_freeObject(jsonReturnValue);
            return true;
         }
         else
         {
            primeStats.totalShares++;
            // the server says no to this share :(
            printf("Server rejected share (BlockHeight: %d/%d nBits: 0x%08X)\n", primecoinBlock->serverData.blockHeight, jhMiner_getCurrentWorkBlockHeight(primecoinBlock->threadIndex), primecoinBlock->serverData.client_shareBits);
            jsonObject_freeObject(jsonReturnValue);
            return false;
         }
      }
      jsonObject_freeObject(jsonReturnValue);
      return false;
   }
   else if( workData.protocolMode == MINER_PROTOCOL_XPUSHTHROUGH )
   {
      // printf("Queue share\n");
      xptShareToSubmit_t* xptShareToSubmit = (xptShareToSubmit_t*)malloc(sizeof(xptShareToSubmit_t));
      memset(xptShareToSubmit, 0x00, sizeof(xptShareToSubmit_t));
      memcpy(xptShareToSubmit->merkleRoot, primecoinBlock->merkleRoot, 32);
      memcpy(xptShareToSubmit->prevBlockHash, primecoinBlock->prevBlockHash, 32);
      xptShareToSubmit->version = primecoinBlock->version;
      xptShareToSubmit->nBits = primecoinBlock->nBits;
      xptShareToSubmit->nonce = primecoinBlock->nonce;
      xptShareToSubmit->nTime = primecoinBlock->timestamp;
      // set multiplier
      CBigNum bnPrimeChainMultiplier;
      bnPrimeChainMultiplier.SetHex(primecoinBlock->mpzPrimeChainMultiplier.get_str(16));
      std::vector<unsigned char> bnSerializeData = bnPrimeChainMultiplier.getvch();
      sint32 lengthBN = bnSerializeData.size();
      memcpy(xptShareToSubmit->chainMultiplier, &bnSerializeData[0], lengthBN);
      xptShareToSubmit->chainMultiplierSize = lengthBN;
      // todo: Set stuff like sieve size
      if( workData.xptClient && !workData.xptClient->disconnected)
         xptClient_foundShare(workData.xptClient, xptShareToSubmit);
      else
      {
         printf("Share submission failed. The client is not connected to the pool.\n");
      }

   }
}

int queryLocalPrimecoindBlockCount(bool useLocal)
{
   sint32 rpcErrorCode = 0;
   jsonObject_t* jsonReturnValue = jsonClient_request(useLocal ? &jsonLocalPrimeCoin : &jsonRequestTarget, "getblockcount", NULL, &rpcErrorCode);
   if( jsonReturnValue == NULL )
   {
      printf("getblockcount() failed with %serror code %d\n", (rpcErrorCode>1000)?"http ":"", rpcErrorCode>1000?rpcErrorCode-1000:rpcErrorCode);
      return 0;
   }
   else
   {
      jsonObject_t* jsonResult = jsonObject_getParameter(jsonReturnValue, "result");
      return (int) jsonObject_getNumberValueAsS32(jsonResult);
      jsonObject_freeObject(jsonReturnValue);
   }

   return 0;
}

static double DIFFEXACTONE = 26959946667150639794667015087019630673637144422540572481103610249215.0;
static const uint64_t diffone = 0xFFFF000000000000ull;

static const unsigned int MAX_PRIMETABLE_SIZE = 250000;

static double target_diff(const unsigned char *target)
{
   double targ = 0;
   signed int i;

   for (i = 31; i >= 0; --i)
      targ = (targ * 0x100) + target[i];

   return DIFFEXACTONE / (targ ? targ: 1);
}


//static double DIFFEXACTONE = 26959946667150639794667015087019630673637144422540572481103610249215.0;
//static const uint64_t diffone = 0xFFFF000000000000ull;

double target_diff(const uint32_t  *target)
{
   double targ = 0;
   signed int i;

   for (i = 0; i < 8; i++)
      targ = (targ * 0x100) + target[7 - i];

   return DIFFEXACTONE / ((double)targ ?  targ : 1);
}


std::string HexBits(unsigned int nBits)
{
   union {
      int32_t nBits;
      char cBits[4];
   } uBits;
   uBits.nBits = htonl((int32_t)nBits);
   return HexStr(BEGIN(uBits.cBits), END(uBits.cBits));
}

static bool IsXptClientConnected()
{
   __try
   {
      if (workData.xptClient == NULL || workData.xptClient->disconnected)
         return false;

   }
   __except(EXCEPTION_EXECUTE_HANDLER)
   {
      return false;
   }
   return true;

}


void jhMiner_queryWork_primecoin()
{
   sint32 rpcErrorCode = 0;
   uint32 time1 = GetTickCount();
   jsonObject_t* jsonReturnValue = jsonClient_request(&jsonRequestTarget, "getwork", NULL, &rpcErrorCode);
   uint32 time2 = GetTickCount() - time1;
   // printf("request time: %dms\n", time2);
   if( jsonReturnValue == NULL )
   {
      printf("Getwork() failed with %serror code %d\n", (rpcErrorCode>1000)?"http ":"", rpcErrorCode>1000?rpcErrorCode-1000:rpcErrorCode);
      workData.workEntry[0].dataIsValid = false;
      return;
   }
   else
   {
      jsonObject_t* jsonResult = jsonObject_getParameter(jsonReturnValue, "result");
      jsonObject_t* jsonResult_data = jsonObject_getParameter(jsonResult, "data");
      //jsonObject_t* jsonResult_hash1 = jsonObject_getParameter(jsonResult, "hash1");
      jsonObject_t* jsonResult_target = jsonObject_getParameter(jsonResult, "target");
      jsonObject_t* jsonResult_serverData = jsonObject_getParameter(jsonResult, "serverData");
      //jsonObject_t* jsonResult_algorithm = jsonObject_getParameter(jsonResult, "algorithm");
      if( jsonResult_data == NULL )
      {
         printf("Error :(\n");
         workData.workEntry[0].dataIsValid = false;
         jsonObject_freeObject(jsonReturnValue);
         return;
      }
      // data
      uint32 stringData_length = 0;
      uint8* stringData_data = jsonObject_getStringData(jsonResult_data, &stringData_length);
      //printf("data: %.*s...\n", (sint32)min(48, stringData_length), stringData_data);

      EnterCriticalSection(&workData.cs);
      yPoolWorkMgr_parseHexString((char*)stringData_data, min(128*2, stringData_length), workData.workEntry[0].data);
      workData.workEntry[0].dataIsValid = true;
      // get server data
      uint32 stringServerData_length = 0;
      uint8* stringServerData_data = jsonObject_getStringData(jsonResult_serverData, &stringServerData_length);
      RtlZeroMemory(workData.workEntry[0].serverData, 32);
      if( jsonResult_serverData )
         yPoolWorkMgr_parseHexString((char*)stringServerData_data, min(128*2, 32*2), workData.workEntry[0].serverData);
      // generate work hash
      uint32 workDataHash = 0x5B7C8AF4;
      for(uint32 i=0; i<stringData_length/2; i++)
      {
         workDataHash = (workDataHash>>29)|(workDataHash<<3);
         workDataHash += (uint32)workData.workEntry[0].data[i];
      }
      workData.workEntry[0].dataHash = workDataHash;
      LeaveCriticalSection(&workData.cs);
      jsonObject_freeObject(jsonReturnValue);
   }
}

/*
* Returns the block height of the most recently received workload
*/
uint32 jhMiner_getCurrentWorkBlockHeight(sint32 threadIndex)
{
   if( workData.protocolMode == MINER_PROTOCOL_GETWORK )
      return ((serverData_t*)workData.workEntry[0].serverData)->blockHeight;	
   else
      return ((serverData_t*)workData.workEntry[threadIndex].serverData)->blockHeight;
}

/*
* Worker thread mainloop for getwork() mode
*/
int jhMiner_workerThread_getwork(int threadIndex)
{
   CSieveOfEratosthenes* psieve = NULL;
   while( true )
   {
      uint8 localBlockData[128];
      // copy block data from global workData
      uint32 workDataHash = 0;
      uint8 serverData[32];
      while( workData.workEntry[0].dataIsValid == false ) Sleep(200);
      EnterCriticalSection(&workData.cs);
      memcpy(localBlockData, workData.workEntry[0].data, 128);
      //seed = workData.seed;
      memcpy(serverData, workData.workEntry[0].serverData, 32);
      LeaveCriticalSection(&workData.cs);
      // swap endianess
      for(uint32 i=0; i<128/4; i++)
      {
         *(uint32*)(localBlockData+i*4) = _swapEndianessU32(*(uint32*)(localBlockData+i*4));
      }
      // convert raw data into primecoin block
      primecoinBlock_t primecoinBlock = {0};
      memcpy(&primecoinBlock, localBlockData, 80);
      // we abuse the timestamp field to generate an unique hash for each worker thread...
      primecoinBlock.timestamp += threadIndex;
      primecoinBlock.threadIndex = threadIndex;
      primecoinBlock.xptMode = (workData.protocolMode == MINER_PROTOCOL_XPUSHTHROUGH);
      // ypool uses a special encrypted serverData value to speedup identification of merkleroot and share data
      memcpy(&primecoinBlock.serverData, serverData, 32);
      // start mining
      if (!BitcoinMiner(&primecoinBlock, psieve, threadIndex))
         break;
      primecoinBlock.mpzPrimeChainMultiplier = 0;
   }
   if( psieve )
   {
      delete psieve;
      psieve = NULL;
   }
   return 0;
}

/*
* Worker thread mainloop for xpt() mode
*/
int jhMiner_workerThread_xpt(int threadIndex)
{
   CSieveOfEratosthenes* psieve = NULL;

   while( true )
   {

      uint8 localBlockData[128];
      // copy block data from global workData
      uint32 workDataHash = 0;
      uint8 serverData[32];
      while( workData.workEntry[threadIndex].dataIsValid == false ) Sleep(50);
      EnterCriticalSection(&workData.cs);
      memcpy(localBlockData, workData.workEntry[threadIndex].data, 128);
      memcpy(serverData, workData.workEntry[threadIndex].serverData, 32);
      workDataHash = workData.workEntry[threadIndex].dataHash;
      LeaveCriticalSection(&workData.cs);
      // convert raw data into primecoin block
      primecoinBlock_t primecoinBlock = {0};
      memcpy(&primecoinBlock, localBlockData, 80);
      // we abuse the timestamp field to generate an unique hash for each worker thread...
      primecoinBlock.timestamp += threadIndex;
      primecoinBlock.threadIndex = threadIndex;
      primecoinBlock.xptMode = (workData.protocolMode == MINER_PROTOCOL_XPUSHTHROUGH);
      // ypool uses a special encrypted serverData value to speedup identification of merkleroot and share data
      memcpy(&primecoinBlock.serverData, serverData, 32);
      // start mining
      //uint32 time1 = GetTickCount();
      if (!BitcoinMiner(&primecoinBlock, psieve, threadIndex))
         break;
      //printf("Mining stopped after %dms\n", GetTickCount()-time1);
      primecoinBlock.mpzPrimeChainMultiplier = 0;
   }
   if( psieve )
   {
      delete psieve;
      psieve = NULL;
   }

   return 0;
}

typedef struct  
{
   char* workername;
   char* workerpass;
   char* host;
   sint32 port;
   sint32 numThreads;
   sint32 sieveSize;
   sint32 numPrimes;
   sint32 primorialMultiplier;
   sint32 targetOverride;
   sint32 targetBTOverride;
   bool printDebug;
   bool enableAutoTune;
}commandlineInput_t;

commandlineInput_t commandlineInput = {0};

void jhMiner_printHelp()
{
   puts("Usage: jhPrimeminer.exe [options]");
   puts("Options:");
   puts("   -o, -O                        The miner will connect to this url");
   puts("                                 You can specifiy an port after the url using -o url:port");
   puts("   -u                            The username (workername) used for login");
   puts("   -p                            The password used for login");
   puts("   -t <num>                      The number of threads for mining (default 1)");
   puts("                                     For most efficient mining, set to number of CPU cores");
   puts("   -s <num>                      Set MaxSieveSize range from 200000 - 10000000");
   puts("                                     Default is 1500000.");
   puts("   -d <num>                      Set Number of primes to weave with - range from 1000 - 250000");
   puts("                                     Default is 15 and it's not recommended to use lower values than 8.");
   puts("                                     It limits how many base primes are used to filter out candidate multipliers in the sieve.");
   puts("   -tune <flag>                  Set a flag to control the auto tune functions");

   puts("Example usage:");
   puts("   jhPrimeminer.exe -o http://www.ypool.net:10034 -u workername.1 -p workerpass");
   puts("Press any key to continue...");
   _getch();
}

void jhMiner_parseCommandline(int argc, char **argv)
{
   sint32 cIdx = 1;
   while( cIdx < argc )
   {
      char* argument = argv[cIdx];
      cIdx++;
      if( memcmp(argument, "-o", 3)==0 || memcmp(argument, "-O", 3)==0 )
      {
         // -o
         if( cIdx >= argc )
         {
            printf("Missing URL after -o option\n");
            ExitProcess(0);
         }
         if( strstr(argv[cIdx], "http://") )
            commandlineInput.host = fStrDup(strstr(argv[cIdx], "http://")+7);
         else
            commandlineInput.host = fStrDup(argv[cIdx]);
         char* portStr = strstr(commandlineInput.host, ":");
         if( portStr )
         {
            *portStr = '\0';
            commandlineInput.port = atoi(portStr+1);
         }
         cIdx++;
      }
      else if( memcmp(argument, "-u", 3)==0 )
      {
         // -u
         if( cIdx >= argc )
         {
            printf("Missing username/workername after -u option\n");
            ExitProcess(0);
         }
         commandlineInput.workername = fStrDup(argv[cIdx], 64);
         cIdx++;
      }
      else if( memcmp(argument, "-p", 3)==0 )
      {
         // -p
         if( cIdx >= argc )
         {
            printf("Missing password after -p option\n");
            ExitProcess(0);
         }
         commandlineInput.workerpass = fStrDup(argv[cIdx], 64);
         cIdx++;
      }
      else if( memcmp(argument, "-t", 3)==0 )
      {
         // -t
         if( cIdx >= argc )
         {
            printf("Missing thread number after -t option\n");
            ExitProcess(0);
         }
         commandlineInput.numThreads = atoi(argv[cIdx]);
         if( commandlineInput.numThreads < 1 || commandlineInput.numThreads > 128 )
         {
            printf("-t parameter out of range");
            ExitProcess(0);
         }
         cIdx++;
      }
      else if( memcmp(argument, "-s", 3)==0 )
      {
         // -s
         if( cIdx >= argc )
         {
            printf("Missing number after -s option\n");
            ExitProcess(0);
         }
         commandlineInput.sieveSize = atoi(argv[cIdx]);
         if( commandlineInput.sieveSize < 2000 || commandlineInput.sieveSize > 100000000 )
         {
            printf("-s parameter out of range, must be between 2000 - 100000000");
            ExitProcess(0);
         }
         cIdx++;
      }
      else if( memcmp(argument, "-d", 3)==0 )
      {
         // -s
         if( cIdx >= argc )
         {
            printf("Missing number after -d option\n");
            ExitProcess(0);
         }
         commandlineInput.numPrimes = atoi(argv[cIdx]);
         if( commandlineInput.numPrimes < 1000 || commandlineInput.numPrimes > MAX_PRIMETABLE_SIZE )
         {
            printf("-d parameter out of range, must be between 1000 - %u", MAX_PRIMETABLE_SIZE);
            ExitProcess(0);
         }
         cIdx++;
      }
      else if( memcmp(argument, "-m", 3)==0 )
      {
         // -primes
         if( cIdx >= argc )
         {
            printf("Missing number after -m option\n");
            ExitProcess(0);
         }
         commandlineInput.primorialMultiplier = atoi(argv[cIdx]);
         if( commandlineInput.primorialMultiplier < 5 || commandlineInput.primorialMultiplier > 1009) 
         {
            printf("-m parameter out of range, must be between 5 - 1009 and should be a prime number");
            ExitProcess(0);
         }
         cIdx++;
      }
      else if( memcmp(argument, "-target", 7)==0 )
      {
         // -target
         if( cIdx >= argc )
         {
            printf("Missing number after -target option\n");
            ExitProcess(0);
         }
         commandlineInput.targetOverride = atoi(argv[cIdx]);
         if( commandlineInput.targetOverride < 0 || commandlineInput.targetOverride > 100 )
         {
            printf("-target parameter out of range, must be between 0 - 100");
            ExitProcess(0);
         }
         cIdx++;
      }
      else if( memcmp(argument, "-bttarget", 9)==0 )
      {
         // -bttarget
         if( cIdx >= argc )
         {
            printf("Missing number after -bttarget option\n");
            ExitProcess(0);
         }
         commandlineInput.targetBTOverride = atoi(argv[cIdx]);
         if( commandlineInput.targetBTOverride < 0 || commandlineInput.targetBTOverride > 100 )
         {
            printf("-bttarget parameter out of range, must be between 0 - 100");
            ExitProcess(0);
         }
         cIdx++;
      }
      else if( memcmp(argument, "-tune", 5)==0 )
      {
         // -tune
         if( cIdx >= argc )
         {
            printf("Missing flag after -tune option\n");
            ExitProcess(0);
         }
         commandlineInput.enableAutoTune = atoi(argv[cIdx]);
         if( commandlineInput.enableAutoTune < 0 || commandlineInput.enableAutoTune > 1 )
         {
            printf("-tune parameter out of range, must be between 0 - 1");
            ExitProcess(0);
         }
         cIdx++;
      }
      else if( memcmp(argument, "-debug", 6)==0 )
      {
         // -debug
         if( cIdx >= argc )
         {
            printf("Missing flag after -debug option\n");
            ExitProcess(0);
         }
         if (memcmp(argument, "true", 5) == 0 ||  memcmp(argument, "1", 2) == 0)
            commandlineInput.printDebug = true;
         cIdx++;
      }
      else if( memcmp(argument, "-help", 6)==0 || memcmp(argument, "--help", 7)==0 )
      {
         jhMiner_printHelp();
         ExitProcess(0);
      }
      else
      {
         printf("'%s' is an unknown option.\nType jhPrimeminer.exe --help for more info\n", argument); 
         ExitProcess(-1);
      }
   }
   if( argc <= 1 )
   {
      jhMiner_printHelp();
      ExitProcess(0);
   }
}

void ResetAutoTuner()
{
   primeStats.bAutoTuneComplete = false; // Auto tune is not finished.
   primeStats.bEnablePrimeTuning = true; // Enable Prime Tuner
   primeStats.bEnableSieveTuning = true; // Enable Sieve Tuner
   primeStats.nAdjustmentsMode = 1; // Start with positive adjustments.
   primeStats.nAdjustmentType = 0; // Start with Prime Count.
   primeStats.nPrimesAdjustmentAmount = nMaxPrimes * 0.10f; // Start Prime adjustments at 10%
   primeStats.nSieveAdjustmentAmount = nMaxSieveSize * 0.25f; // Start Sieve size adjustments at 25%
   primeStats.nMaxPrimesAdjustmentAmount = primeStats.nMaxSieveAdjustmentAmount = 0;
}

void ResetPrimeStatistics()
{
   primeStats.blockStartTime = primeStats.startTime = GetTickCount();
   primeStats.shareFound = false;
   primeStats.shareRejected = false;
   primeStats.nCandidateCount = 0;
   primeStats.foundShareCount = 0;
   for(int i = 0; i < sizeof(primeStats.chainCounter[0])/sizeof(uint32);  i++)
   {
      primeStats.chainCounter[0][i] = 0;
      primeStats.chainCounter[1][i] = 0;
      primeStats.chainCounter[2][i] = 0;
      primeStats.chainCounter[3][i] = 0;
   }
   primeStats.validShares = 0;
   primeStats.totalShares = 0;
   primeStats.fShareValue = 0;
   primeStats.fBlockShareValue = 0;
   primeStats.fTotalSubmittedShareValue = 0;
   primeStats.bestPrimeChainDifficulty = 0;
   primeStats.bestPrimeChainDifficultySinceLaunch = 0;
   primeStats.nSieveRounds = 0;
}

void PrintCurrentSettings()
{
   unsigned long uptime = (GetTickCount() - primeStats.startTime);

   unsigned int days = uptime / (24 * 60 * 60 * 1000);
   uptime %= (24 * 60 * 60 * 1000);
   unsigned int hours = uptime / (60 * 60 * 1000);
   uptime %= (60 * 60 * 1000);
   unsigned int minutes = uptime / (60 * 1000);
   uptime %= (60 * 1000);
   unsigned int seconds = uptime / (1000);

   printf("\n\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\n");	
   printf("Worker name (-u): %s\n", commandlineInput.workername);
   printf("Number of mining threads (-t): %u\n", commandlineInput.numThreads);
   printf("Sieve Size (-s): %u\n", nMaxSieveSize);
   printf("Primes Used (-d): %u\n", nMaxPrimes);
   printf("Primorial Multiplier (-m): %u\n", primeStats.nPrimorialMultiplier);
   printf("Chain Length Target (-target): %u\n", nOverrideTargetValue);	
   printf("BiTwin Length Target (-bttarget): %u\n", nOverrideBTTargetValue);	
   if (nEnableAutoTune)
   {
      printf("Auto Tune: %s\n", (primeStats.bAutoTuneComplete) ? "enabled (Completed)" : "enabled (In Progress)" );	
   }
   else
   {
      printf("Auto Tune: disabled\n");	
   }
   printf("Total Runtime: %u Days, %u Hours, %u minutes, %u seconds\n", days, hours, minutes, seconds);	
   printf("Total Share Value submitted to the Pool: %.05f\n", primeStats.fTotalSubmittedShareValue);	
   printf("\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\n\n");
}



bool appQuitSignal = false;

static void input_thread()
{
   while (true) 
   {
      int input;
      input = _getch();		
      switch (input) {
      case 'q': case 'Q': case 3: //case 27:
         appQuitSignal = true;
         Sleep(3200);
         std::exit(0);
         return;
         break;
      case '[':
         if (!PrimeTableGetPreviousPrime((unsigned int) primeStats.nPrimorialMultiplier))
            error("PrimecoinMiner() : primorial decrement overflow");	
         printf("Primorial Multiplier: %u\n", primeStats.nPrimorialMultiplier);
         break;
      case ']':
         if (!PrimeTableGetNextPrime((unsigned int)  primeStats.nPrimorialMultiplier))
            error("PrimecoinMiner() : primorial increment overflow");
         printf("Primorial Multiplier: %u\n", primeStats.nPrimorialMultiplier);
         break;
      case 's': case 'S':			
         PrintCurrentSettings();
         break;
      case 't': case 'T':			
         nEnableAutoTune = !nEnableAutoTune;
         if (nEnableAutoTune)
         {
            // Reset tuning params.
            ResetAutoTuner();
         }
         printf("Auto Tuner %s\n", (nEnableAutoTune) ? "enabled" : "disabled");
         break;
      case 'r': case 'R':			
         ResetPrimeStatistics();
         printf("All mining statistics reset.");
         break;
      case '+': case '=':
         if (nMaxSieveSize < 10000000)
            nMaxSieveSize += 100000;
         printf("Sieve size: %u\n", nMaxSieveSize);
         break;
      case '-':
         if (nMaxSieveSize > 100000)
            nMaxSieveSize -= 100000;
         printf("Sieve size: %u\n", nMaxSieveSize);
         break;
      case 0: case 224:
         {
            input = _getch();	
            switch (input)
            {
            case 72: // key up
               if (nMaxPrimes < MAX_PRIMETABLE_SIZE)
                  nMaxPrimes ++;
               printf("Primes Used: %u%%\n", nMaxPrimes);
               break;

            case 80: // key down
               if (nMaxPrimes > 1000)
                  nMaxPrimes --;
               printf("Primes used: %u%%\n", nMaxPrimes);
               break;

            case 77:    // key right
               if (nMaxPrimes < MAX_PRIMETABLE_SIZE) nMaxPrimes += 1000;
               if (nMaxPrimes > MAX_PRIMETABLE_SIZE) nMaxPrimes = MAX_PRIMETABLE_SIZE;
               printf("Primes Used: %u%%\n", nMaxPrimes);
               break;
            case 75:    // key left
               if (nMaxPrimes > 1000) nMaxPrimes -= 1000;
               if (nMaxPrimes < 1000) nMaxPrimes = 1000;
               printf("Primes used: %u%%\n", nMaxPrimes);
               break;
            }
         }

      }
      Sleep(20);
   }

   return;
}

typedef std::pair <DWORD, HANDLE> thMapKeyVal;
DWORD * threadHearthBeat;

static void watchdog_thread(std::map<DWORD, HANDLE> threadMap)
{
   DWORD maxIdelTime = 30 * 1000; // Allow 30 secs of "idle" time between heartbeats before a thread is deemed "dead".
   std::map <DWORD, HANDLE> :: const_iterator thMap_Iter;
   while(true)
   {
      if ((workData.protocolMode == MINER_PROTOCOL_XPUSHTHROUGH) && (!IsXptClientConnected()))
      {
         // Miner is not connected, wait 5 secs before trying again.
         Sleep(5000);
         continue;
      }

      DWORD currentTick = GetTickCount();

      for (int i = 0; i < threadMap.size(); i++)
      {
         DWORD heartBeatTick = threadHearthBeat[i];
         if (1 == 0 && (currentTick - heartBeatTick > maxIdelTime))
         {
            //restart the thread
            printf("Restarting thread %d\n", i);
            //__try
            //{

            //HANDLE h = threadMap.at(i);
            thMap_Iter = threadMap.find(i);
            if (thMap_Iter != threadMap.end())
            {
               HANDLE h = thMap_Iter->second;
               TerminateThread( h, 0);
               Sleep(1000);
               CloseHandle(h);
               Sleep(1000);
               threadHearthBeat[i] = GetTickCount();
               threadMap.erase(thMap_Iter);

               h = CreateThread(NULL, 0, (LPTHREAD_START_ROUTINE)jhMiner_workerThread_xpt, (LPVOID)i, 0, 0);
               SetThreadPriority(h, THREAD_PRIORITY_BELOW_NORMAL);

               threadMap.insert(thMapKeyVal(i,h));

            }
            /*}
            __except(EXCEPTION_EXECUTE_HANDLER)
            {
            }*/
         }
      }
      Sleep( 1*1000);
   }
}


/*
* Mainloop when using getwork() mode
*/
int jhMiner_main_getworkMode()
{
   // start the Auto Tuning thread
   CreateThread(NULL, 0, (LPTHREAD_START_ROUTINE)input_thread, NULL, 0, 0);

   // start threads
   // Although we create all the required heartbeat structures, there is no heartbeat watchdog in GetWork mode. 
   std::map<DWORD, HANDLE> threadMap;
   threadHearthBeat = (DWORD *)malloc( commandlineInput.numThreads * sizeof(DWORD));
   // start threads
   for(sint32 threadIdx=0; threadIdx<commandlineInput.numThreads; threadIdx++)
   {
      HANDLE hThread = CreateThread(NULL, 0, (LPTHREAD_START_ROUTINE)jhMiner_workerThread_getwork, (LPVOID)threadIdx, 0, 0);
      SetThreadPriority(hThread, THREAD_PRIORITY_BELOW_NORMAL);
      threadMap.insert(thMapKeyVal(threadIdx,hThread));
      threadHearthBeat[threadIdx] = GetTickCount();
   }

   // main thread, query work every 8 seconds
   sint32 loopCounter = 0;
   while( true )
   {
      // query new work
      jhMiner_queryWork_primecoin();
      // calculate stats every second tick
      if( loopCounter&1 )
      {
         double statsPassedTime = (double)(GetTickCount() - primeStats.blockStartTime);
         if( statsPassedTime < 1.0 )
            statsPassedTime = 1.0; // avoid division by zero
         double primesPerSecond = (double)primeStats.nCandidateCount / (statsPassedTime / 1000.0);
         primeStats.blockStartTime = GetTickCount();
         primeStats.nCandidateCount = 0;
         uint32 bestDifficulty = primeStats.bestPrimeChainDifficulty;
         primeStats.bestPrimeChainDifficulty = 0;
         double primeDifficulty = (double)bestDifficulty / (double)0x1000000;
         if( workData.workEntry[0].dataIsValid )
         {
            primeStats.bestPrimeChainDifficultySinceLaunch = max(primeStats.bestPrimeChainDifficultySinceLaunch, primeDifficulty);
            printf("primes/s: %d best difficulty: %f record: %f\n", (sint32)primesPerSecond, (float)primeDifficulty, (float)primeStats.bestPrimeChainDifficultySinceLaunch);
         }
      }		
      // wait and check some stats
      uint32 time_updateWork = GetTickCount();
      while( true )
      {
         uint32 passedTime = GetTickCount() - time_updateWork;
         if( passedTime >= 4000 )
            break;
         Sleep(200);
      }
      loopCounter++;
   }
   return 0;
}

/*
* Mainloop when using xpt mode
*/
int jhMiner_main_xptMode()
{
   std::ofstream shareLog;
   shareLog.open("FoundShares.log", std::ios::out | std::ios::app);
   if (shareLog.is_open())
   {
      time_t now = time(0);
      struct tm * timeinfo;
      timeinfo = localtime (&now);
      char sNow [80];
      strftime (sNow, 80, "%x-%X",timeinfo);

      shareLog << "*=============================================================================================\n";
      shareLog << "*MINER STARTED @ " << sNow << "\t" << commandlineInput.numThreads << "\n";
      shareLog << "*=============================================================================================\n";
      shareLog << "I" << nMaxSieveSize << "\t" << nMaxPrimes << "\t" << primeStats.nSieveLayers << "\n";
      shareLog.close();
   }

   // start the Auto Tuning thread
   CreateThread(NULL, 0, (LPTHREAD_START_ROUTINE)input_thread, NULL, 0, 0);


   std::map<DWORD, HANDLE> threadMap;
   threadHearthBeat = (DWORD *)malloc( commandlineInput.numThreads * sizeof(DWORD));
   // start threads
   for(sint32 threadIdx=0; threadIdx<commandlineInput.numThreads; threadIdx++)
   {
      HANDLE hThread = CreateThread(NULL, 0, (LPTHREAD_START_ROUTINE)jhMiner_workerThread_xpt, (LPVOID)threadIdx, 0, 0);
      SetThreadPriority(hThread, THREAD_PRIORITY_BELOW_NORMAL);
      threadMap.insert(thMapKeyVal(threadIdx,hThread));
      threadHearthBeat[threadIdx] = GetTickCount();
   }

   CreateThread(NULL, 0, (LPTHREAD_START_ROUTINE)watchdog_thread, (LPVOID)&threadMap, 0, 0);


   // main thread, don't query work, just wait and process
   uint32 xptWorkIdentifier = 0xFFFFFFFF;
   while( true )
   {
      if (appQuitSignal)
         return 0;

      // Exit after 5 min
      //if ((double)(GetTickCount() - primeStats.startTime) > 300000) return 0;


      xptClient_process(workData.xptClient);
      char* disconnectReason = false;
      if( workData.xptClient == NULL || xptClient_isDisconnected(workData.xptClient, &disconnectReason) )
      {
         // disconnected, mark all data entries as invalid
         for(uint32 i=0; i<128; i++)
            workData.workEntry[i].dataIsValid = false;
         printf("xpt: Disconnected, auto reconnect in 30 seconds\n");
         if( workData.xptClient && disconnectReason )
            printf("xpt: Disconnect reason: %s\n", disconnectReason);
         Sleep(30*1000);
         if( workData.xptClient )
            xptClient_free(workData.xptClient);
         xptWorkIdentifier = 0xFFFFFFFF;
         while( true )
         {
            workData.xptClient = xptClient_connect(&jsonRequestTarget, commandlineInput.numThreads);
            if( workData.xptClient )
               break;
         }
      }
      // has the block data changed?
      if( workData.xptClient && xptWorkIdentifier != workData.xptClient->workDataCounter )
      {
         // printf("New work\n");
         xptWorkIdentifier = workData.xptClient->workDataCounter;
         for(uint32 i=0; i<workData.xptClient->payloadNum; i++)
         {
            uint8 blockData[256];
            memset(blockData, 0x00, sizeof(blockData));
            *(uint32*)(blockData+0) = workData.xptClient->blockWorkInfo.version;
            memcpy(blockData+4, workData.xptClient->blockWorkInfo.prevBlock, 32);
            memcpy(blockData+36, workData.xptClient->workData[i].merkleRoot, 32);
            *(uint32*)(blockData+68) = workData.xptClient->blockWorkInfo.nTime;
            *(uint32*)(blockData+72) = workData.xptClient->blockWorkInfo.nBits;
            *(uint32*)(blockData+76) = 0; // nonce
            memcpy(workData.workEntry[i].data, blockData, 80);
            ((serverData_t*)workData.workEntry[i].serverData)->blockHeight = workData.xptClient->blockWorkInfo.height;
            ((serverData_t*)workData.workEntry[i].serverData)->nBitsForShare = workData.xptClient->blockWorkInfo.nBitsShare;

            // is the data really valid?
            if( workData.xptClient->blockWorkInfo.nTime > 0 )
               workData.workEntry[i].dataIsValid = true;
            else
               workData.workEntry[i].dataIsValid = false;
         }
         if (workData.xptClient->blockWorkInfo.height > 0)
         {
            const unsigned long reportTime = GetTickCount();
            double totalRunTime = (double)(reportTime - primeStats.startTime);
            double blockPassedTime = (double)(reportTime - primeStats.blockStartTime);
            if( blockPassedTime < 1.0 ) blockPassedTime = 1.0; // avoid division by zero
            double poolDiff = GetPrimeDifficulty( workData.xptClient->blockWorkInfo.nBitsShare);
            double blockDiff = GetPrimeDifficulty( workData.xptClient->blockWorkInfo.nBits);
            double primesPerSecond = (double)primeStats.nCandidateCount / (blockPassedTime / 1000.0);
            float shareValuePerHour = primeStats.fShareValue / totalRunTime * 3600000.0;
            float avgCandidatesPerRound = (double)primeStats.nCandidateCount / ((primeStats.nSieveRounds > 0) ? primeStats.nSieveRounds : 1);
            float weavesPerSecond = (double)primeStats.nSieveRounds / (blockPassedTime / 1000.0);
            float primeDifficulty = GetChainDifficulty(primeStats.bestPrimeChainDifficulty);
            double numsTestedPerSecond = ((double)nMaxSieveSize / 2) * primeStats.nSieveLayers * weavesPerSecond;

            time_t now = time(0);
            struct tm * timeinfo;
            timeinfo = localtime (&now);
            char sNow [80];
            strftime (sNow, 80, "%x-%X",timeinfo);

            primeStats.bestPrimeChainDifficultySinceLaunch = max(primeStats.bestPrimeChainDifficultySinceLaunch, primeDifficulty);
            printf("\n\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\n");
            printf("%s - New Block: %u - Diff: %.06f / %.06f\n", sNow, workData.xptClient->blockWorkInfo.height, blockDiff, poolDiff);
            printf("Valid/Total shares: [ %d / %d ]  -  Best/Max diff: [ %.06f / %.06f ]\n",primeStats.validShares, primeStats.totalShares, primeStats.bestPrimeChainDifficultySinceLaunch, primeDifficulty);
            printf("Share Value - Total/Per Hour/Last Block: [ %0.6f / %0.6f / %0.6f ]\n", primeStats.fTotalSubmittedShareValue, shareValuePerHour, primeStats.fBlockShareValue);
            for (int i = 6; i <= max(6,(int)primeStats.bestPrimeChainDifficultySinceLaunch); i++)
            {
               double sharePerHour = ((double)primeStats.chainCounter[0][i] / totalRunTime) * 3600000.0;
               printf("%2dch/h: %8.02f - %u [ %u / %u / %u ]\n", // - Val: %0.06f\n", 
                  i, sharePerHour, 
                  primeStats.chainCounter[0][i],
                  primeStats.chainCounter[1][i],
                  primeStats.chainCounter[2][i],
                  primeStats.chainCounter[3][i]//, 
               //(double)primeStats.chainCounter[0][i] * GetValueOfShareMajor(i)
               );
            }
            printf("NPS:%-12d PPS:%-12d WPS:%-8.03f ACC:%-8d\n", (sint32)numsTestedPerSecond, (sint32)primesPerSecond, weavesPerSecond, (sint32)avgCandidatesPerRound);
            printf("Current Primorial: %u - Sieve Size: %u - Prime Count: %u\n", primeStats.nPrimorialMultiplier, nMaxSieveSize, nMaxPrimes);

            // Reset all the prime stats
            primeStats.blockStartTime = GetTickCount();
            primeStats.bestPrimeChainDifficulty = 0;
            primeStats.fBlockShareValue = 0;
            primeStats.nCandidateCount = 0;
            primeStats.nSieveRounds = 0;
            multiplierSet.clear();

            // Perform adjustments to boost speed.
            if ((blockPassedTime >= 10000) && (nEnableAutoTune))
            {
               if (primeStats.bAutoTuneComplete)
               {
                  if (primeStats.nBestNumbersTestedPerSecond > 0) 
                  {
                     if ((abs((double)primeStats.nBestNumbersTestedPerSecond - numsTestedPerSecond)/ primeStats.nBestNumbersTestedPerSecond) > 0.65)
                     {
                        // Last block is more than 35% diff to recorded best, something about machine usage has changed.
                        // Issue a new auto tune.
                        ResetAutoTuner();
                        printf("Large performance change detected, restarting auto tuner\n");
                     }
                  }
               }
               else
               {
                  if (numsTestedPerSecond > primeStats.nBestNumbersTestedPerSecond)
                  {
                     if (primeStats.nBestNumbersTestedPerSecond > 0) printf("New Best results recorded! - ");
                     primeStats.nBestNumbersTestedPerSecond = numsTestedPerSecond;
                     primeStats.nBestPrimorialMultiplier = primeStats.nPrimorialMultiplier;
                     primeStats.nBestPrimeCount = nMaxPrimes;
                     primeStats.nBestSieveSize = nMaxSieveSize;
                  }

                  bool switchAdjustment = false;
                  if (numsTestedPerSecond > (primeStats.nLastNumbersTestedPerSecond * 0.95f))// ignore up to a 5% slowdown as "variance"
                  {
                     if (numsTestedPerSecond > primeStats.nLastNumbersTestedPerSecond)
                     {
                        primeStats.nLastNumbersTestedPerSecond = numsTestedPerSecond; 
                     }

                     if (primeStats.nAdjustmentType)
                     {
                        const int adjAmount = ((int)primeStats.nSieveAdjustmentAmount * primeStats.nAdjustmentsMode);
                        const int totalAdjustment = abs((int)primeStats.nBestSieveSize - (int)(nMaxSieveSize + adjAmount));
                        if (((primeStats.nMaxSieveAdjustmentAmount == 0) || (totalAdjustment <= primeStats.nMaxSieveAdjustmentAmount))
                           && (nMaxSieveSize > 1000))
                        {
                           nMaxSieveSize += adjAmount;
                           if (nMaxSieveSize < 1000) nMaxSieveSize = 1000;
                           printf("New Sieve Size: %u", nMaxSieveSize);
                        }
                        else
                        {
                           switchAdjustment = true;
                        }
                     }
                     else
                     {
                        const int adjAmount = ((int)primeStats.nPrimesAdjustmentAmount * primeStats.nAdjustmentsMode);
                        const int totalAdjustment = abs((int)primeStats.nBestPrimeCount - (int)(nMaxPrimes + adjAmount));
                        if (((primeStats.nMaxPrimesAdjustmentAmount == 0) || (totalAdjustment <= primeStats.nMaxPrimesAdjustmentAmount))
                           && ((nMaxPrimes > 1000) && (nMaxPrimes < MAX_PRIMETABLE_SIZE)))
                        {
                           nMaxPrimes += adjAmount;
                           if (nMaxPrimes > MAX_PRIMETABLE_SIZE) nMaxPrimes = MAX_PRIMETABLE_SIZE;
                           if (nMaxPrimes < 1000) nMaxPrimes = 1000;
                           printf("New Primes Count: %u", nMaxPrimes);
                        }
                        else
                        {
                           switchAdjustment = true;
                        }
                     }
                  }
                  else
                  {
                     switchAdjustment = true;
                  }

                  if (switchAdjustment)
                  {
                     primeStats.nLastNumbersTestedPerSecond = 0;
                     primeStats.nBestNumbersTestedPerSecond = 0; // Debateable
                     primeStats.nPrimorialMultiplier = primeStats.nBestPrimorialMultiplier;
                     nMaxPrimes = primeStats.nBestPrimeCount;
                     nMaxSieveSize = primeStats.nBestSieveSize;
                     printf("Resetting to previous best. Sieve Size: %u - Prime Count: %u", nMaxSieveSize, nMaxPrimes);
                     primeStats.nAdjustmentsMode *= -1;
                     if (primeStats.nAdjustmentsMode > 0)
                     {
                        if (primeStats.nAdjustmentType)
                        {
                           if (primeStats.nSieveAdjustmentAmount == 1000) primeStats.bEnableSieveTuning = false;
                           primeStats.nMaxSieveAdjustmentAmount = (2 * primeStats.nSieveAdjustmentAmount);

                           primeStats.nSieveAdjustmentAmount = (ceil((primeStats.nSieveAdjustmentAmount * 0.50f)/1000) * 1000);
                           if (primeStats.nSieveAdjustmentAmount < 1000) primeStats.nSieveAdjustmentAmount = 1000;
                        }
                        else
                        {
                           if (primeStats.nPrimesAdjustmentAmount == 1) primeStats.bEnablePrimeTuning = false;
                           primeStats.nMaxPrimesAdjustmentAmount = (2 * primeStats.nPrimesAdjustmentAmount);

                           primeStats.nPrimesAdjustmentAmount *= 0.50f;
                           if (primeStats.nPrimesAdjustmentAmount < 1) primeStats.nPrimesAdjustmentAmount = 1;
                        }
                        if (primeStats.bEnablePrimeTuning == false && primeStats.bEnableSieveTuning == false)
                        {
                           primeStats.bAutoTuneComplete = true;
                           printf("\nAuto tuning complete.");
                        }
                        else
                        {
                           primeStats.nAdjustmentType = (primeStats.nAdjustmentType == 0) ? 1 : 0; // Switch adjustment mode.
                           if ((primeStats.nAdjustmentType) && (!primeStats.bEnableSieveTuning)) primeStats.nAdjustmentType = 0;
                           if ((!primeStats.nAdjustmentType) && (!primeStats.bEnablePrimeTuning)) primeStats.nAdjustmentType = 1;
                        }
                     }
                  }
                  printf("\n");

                  std::ofstream shareLog;
                  shareLog.open("FoundShares.log", std::ios::out | std::ios::app);
                  if (shareLog.is_open())
                  {
                     shareLog << "I" << nMaxSieveSize << "\t" << nMaxPrimes << "\t" << primeStats.nSieveLayers << "\n";
                     shareLog.close();
                  }

               }
            }
            printf("\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\n");

         }
      }
      Sleep(10);
   }

   return 0;
}

int main(int argc, char **argv)
{
   // setup some default values
   commandlineInput.port = 10034;
   SYSTEM_INFO sysinfo;
   GetSystemInfo( &sysinfo );
   commandlineInput.numThreads = sysinfo.dwNumberOfProcessors;
   commandlineInput.numThreads = max(commandlineInput.numThreads, 1);
   commandlineInput.sieveSize = 1024000; // default maxSieveSize
   commandlineInput.numPrimes = 25000; // default 
   commandlineInput.primorialMultiplier = 61; // for default we use 61
   commandlineInput.targetOverride = 0;
   commandlineInput.targetBTOverride = 0;
   commandlineInput.printDebug = 0;
   commandlineInput.enableAutoTune = 1;

   // parse command lines
   jhMiner_parseCommandline(argc, argv);
   // Sets max sieve size
   nMaxSieveSize = commandlineInput.sieveSize;
   nMaxPrimes = commandlineInput.numPrimes;
   nOverrideTargetValue = commandlineInput.targetOverride;
   nOverrideBTTargetValue = commandlineInput.targetBTOverride;
   nEnableAutoTune = commandlineInput.enableAutoTune;

   if( commandlineInput.host == NULL )
   {
      printf("Missing -o option\n");
      ExitProcess(-1);	
   }

   //CRYPTO_set_mem_ex_functions(mallocEx, reallocEx, freeEx);

   printf("\n");
   printf("\xC9\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xBB\n");
   printf("\xBA  jhPrimeMiner - mod by rdebourbon -v4.0d beta                 \xBA\n");
   printf("\xBA  author: JH (http://ypool.net)                                \xBA\n");
   printf("\xBA                                                               \xBA\n");
   printf("\xBA  Credits: Sunny King for the original Primecoin client&miner  \xBA\n");
   printf("\xBA  Credits: mikaelh for the performance optimizations           \xBA\n");
   printf("\xBA                                                               \xBA\n");
   printf("\xBA  Donations:                                                   \xBA\n");
   printf("\xBA        XPM: AUwKMCYCacE6Jq1rsLcSEHSNiohHVVSiWv                \xBA\n");
   printf("\xBA        LTC: LV7VHT3oGWQzG9EKjvSXd3eokgNXj6ciFE                \xBA\n");
   printf("\xBA        BTC: 1Fph7y622HJ5Cwq4bkzfeZXWep2Jyi5kp7                \xBA\n");
   printf("\xC8\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xCD\xBC\n");
   printf("Launching miner...\n");
   // set priority lower so the user still can do other things
   SetPriorityClass(GetCurrentProcess(), BELOW_NORMAL_PRIORITY_CLASS);
   // init memory speedup (if not already done in preMain)
   //mallocSpeedupInit();
   if( pctx == NULL )
      pctx = BN_CTX_new();
   // init prime table
   GeneratePrimeTable(MAX_PRIMETABLE_SIZE);
   printf("Primes Used: %u %%\n", nMaxPrimes);
   // init winsock
   WSADATA wsa;
   WSAStartup(MAKEWORD(2,2),&wsa);
   // init critical section
   InitializeCriticalSection(&workData.cs);
   // connect to host
   hostent* hostInfo = gethostbyname(commandlineInput.host);
   if( hostInfo == NULL )
   {
      printf("Cannot resolve '%s'. Is it a valid URL?\n", commandlineInput.host);
      ExitProcess(-1);
   }
   void** ipListPtr = (void**)hostInfo->h_addr_list;
   uint32 ip = 0xFFFFFFFF;
   if( ipListPtr[0] )
   {
      ip = *(uint32*)ipListPtr[0];
   }
   char ipText[32];
   esprintf(ipText, "%d.%d.%d.%d", ((ip>>0)&0xFF), ((ip>>8)&0xFF), ((ip>>16)&0xFF), ((ip>>24)&0xFF));
   if( ((ip>>0)&0xFF) != 255 )
   {
      printf("Connecting to '%s' (%d.%d.%d.%d)\n", commandlineInput.host, ((ip>>0)&0xFF), ((ip>>8)&0xFF), ((ip>>16)&0xFF), ((ip>>24)&0xFF));
   }
   // setup RPC connection data (todo: Read from command line)
   jsonRequestTarget.ip = ipText;
   jsonRequestTarget.port = commandlineInput.port;
   jsonRequestTarget.authUser = commandlineInput.workername;
   jsonRequestTarget.authPass = commandlineInput.workerpass;

   jsonLocalPrimeCoin.ip = "127.0.0.1";
   jsonLocalPrimeCoin.port = 9912;
   jsonLocalPrimeCoin.authUser = "primecoinrpc";
   jsonLocalPrimeCoin.authPass = "x";

   //lastBlockCount = queryLocalPrimecoindBlockCount(useLocalPrimecoindForLongpoll);

   // init stats
   primeStats.nPrimorialMultiplier = commandlineInput.primorialMultiplier;
   ResetPrimeStatistics();
   ResetAutoTuner();

   // setup thread count and print info
   printf("Using %d threads\n", commandlineInput.numThreads);
   printf("Username: %s\n", jsonRequestTarget.authUser);
   printf("Password: %s\n", jsonRequestTarget.authPass);
   // decide protocol
   if( commandlineInput.port == 10034 )
   {
      // port 10034 indicates xpt protocol (in future we will also add a -o URL prefix)
      workData.protocolMode = MINER_PROTOCOL_XPUSHTHROUGH;
      printf("Using x.pushthrough protocol\n");
   }
   else
   {
      workData.protocolMode = MINER_PROTOCOL_GETWORK;
      printf("Using GetWork() protocol\n");
      printf("Warning: \n");
      printf("   GetWork() is outdated and inefficient. You are losing mining performance\n");
      printf("   by using it. If the pool supports it, consider switching to x.pushthrough.\n");
      printf("   Just add the port :10034 to the -o parameter.\n");
      printf("   Example: jhPrimeminer.exe -o http://poolurl.net:10034 ...\n");
   }
   // initial query new work / create new connection
   if( workData.protocolMode == MINER_PROTOCOL_GETWORK )
   {
      jhMiner_queryWork_primecoin();
   }
   else if( workData.protocolMode == MINER_PROTOCOL_XPUSHTHROUGH )
   {
      workData.xptClient = NULL;
      // x.pushthrough initial connect & login sequence
      while( true )
      {
         // repeat connect & login until it is successful (with 30 seconds delay)
         while ( true )
         {
            workData.xptClient = xptClient_connect(&jsonRequestTarget, commandlineInput.numThreads);
            if( workData.xptClient != NULL )
               break;
            printf("Failed to connect, retry in 30 seconds\n");
            Sleep(1000*30);
         }
         // make sure we are successfully authenticated
         while( xptClient_isDisconnected(workData.xptClient, NULL) == false && xptClient_isAuthenticated(workData.xptClient) == false )
         {
            xptClient_process(workData.xptClient);
            Sleep(1);
         }
         char* disconnectReason = NULL;
         // everything went alright?
         if( xptClient_isDisconnected(workData.xptClient, &disconnectReason) == true )
         {
            xptClient_free(workData.xptClient);
            workData.xptClient = NULL;
            break;
         }
         if( xptClient_isAuthenticated(workData.xptClient) == true )
         {
            break;
         }
         if( disconnectReason )
            printf("xpt error: %s\n", disconnectReason);
         // delete client
         xptClient_free(workData.xptClient);
         // try again in 30 seconds
         printf("x.pushthrough authentication sequence failed, retry in 30 seconds\n");
         Sleep(30*1000);
      }
   }

   printf("\nNPS = 'Numbers tested per Second', PPS = 'Primes Per Second', \n");
   printf("WPS = 'Weaves Per Second', ACC = 'Avg. Candidate Count per weave' \n");
   printf("===============================================================\n");
   printf("Keyboard shortcuts:\n");
   printf("   <Ctrl-C>, <Q>     - Quit\n");
   printf("   <Up arrow key>    - Increment Prime Count by 1\n");
   printf("   <Down arrow key>  - Decrement Prime Count by 1\n");
   printf("   <Left arrow key>  - Decrement Prime Count by 1000\n");
   printf("   <Right arrow key> - Increment Prime Count by 1000\n");
   printf("   <S> - Print current settings\n");
   printf("   <R> - Reset all statistics\n");
   printf("   <T> - Enable/Disable Auto tuning\n");
   printf("   <[> - Decrement Primorial Multiplier\n");
   printf("   <]> - Increment Primorial Multiplier\n");
   printf("   <-> - Decrement Sieve size\n");
   printf("   <+> - Increment Sieve size\n");


   // enter different mainloops depending on protocol mode
   if( workData.protocolMode == MINER_PROTOCOL_GETWORK )
      return jhMiner_main_getworkMode();
   else if( workData.protocolMode == MINER_PROTOCOL_XPUSHTHROUGH )
      return jhMiner_main_xptMode();

   return 0;
}

///*
// * We need to call this before the actual initialization of the bignum constants in prime.h and other files
// */
//int preMain_initCryptoMemFunctions()
//{
//	//mallocSpeedupInit();
//	/*CRYPTO_set_mem_ex_functions(mallocEx, reallocEx, freeEx);
//	CRYPTO_set_mem_debug_functions(NULL, NULL, NULL, NULL, NULL);*/
//	// See comment above mallocEx() method
//	return 0;
//}
//
//typedef int cb(void);
//
//#pragma data_seg(".CRT$XIU")
//static cb *autostart[] = { preMain_initCryptoMemFunctions };
//
//#pragma data_seg() /* reset data-segment */

/*
void debug_getSieveDataHash(CSieveOfEratosthenes* sieve, uint8* hashOut)
{
sha256_context ctx;
sha256_starts(&ctx);
sha256_update(&ctx, (uint8*)sieve->vfCompositeCunningham1, (nMaxSieveSize+7)/8);
sha256_update(&ctx, (uint8*)sieve->vfCompositeCunningham2, (nMaxSieveSize+7)/8);
sha256_update(&ctx, (uint8*)sieve->vfCompositeBiTwin, (nMaxSieveSize+7)/8);
sha256_finish(&ctx, hashOut);
}
*/

//
//int mainPerformanceTest()
//{
//	GeneratePrimeTable();
//	// performance test for sieve generation
//	sint32 sieveSize = 1000000;
//	uint32 nBits = 0x07fb8bcc;
//	uint256 blockHashHeader;
//	yPoolWorkMgr_parseHexString("eed69c071ac2634ffc2a9e73177d1c5fad92fdf06f6d711c2f04877906ad6aef", 32*2, blockHashHeader.begin());
//	CBigNum fixedMultiplier = CBigNum(0xB);
//
//	uint8 orgSieveHash[32];
//	uint8 fastSieveHash[32];
//
//	printf("Generating original sieve and fast sieve...\n");
//	uint32 time1 = GetTickCount();
//	CSieveOfEratosthenes* originalSieve = new CSieveOfEratosthenes(sieveSize, nBits, blockHashHeader, fixedMultiplier);
//	while (originalSieve->WeaveOriginal() );
//	uint32 time2 = GetTickCount();
//	printf("Original sieve time: %8dms Hash: ", time2-time1);
//	debug_getSieveDataHash(originalSieve, orgSieveHash);
//	for(uint32 i=0; i<12; i++)
//		printf("%02x", orgSieveHash[i]);
//	puts("");
//	puts("Start generating fast sieve...\n");
//	uint32 time3 = GetTickCount();
//	CSieveOfEratosthenes* fastSieve = new CSieveOfEratosthenes(sieveSize, nBits, blockHashHeader, fixedMultiplier);
//	//while (fastSieve->WeaveFast2() );
//	fastSieve->WeaveFastAll();
//	uint32 time4 = GetTickCount();
//	printf("Fast sieve time:     %8dms Hash: ", time4-time3);
//	debug_getSieveDataHash(fastSieve, fastSieveHash);
//	for(uint32 i=0; i<12; i++)
//		printf("%02x", fastSieveHash[i]);
//	puts("");
//	while( true ) Sleep(1000);
//	return 0;
//}
