#include <stdio.h>
#include <stdlib.h>

#include "tinyscript/ast.h"
#include "tinyscript/interp.h"
#include "tinyscript/sectypes.h"
#include "common/csapp.h"
#include "common/safemem.h"

int yywrap() { return 1; }

extern char pbuf[MAXLINE];
prog *parse_buf(char *buf, long len);

prog SANDBOX_SECTION *program;
state_t SANDBOX_SECTION *s;

sec_lattice* L;
sec_ctxt* G;
char labelfile[1000];

int findLabel(sec_lattice *L,char* ident) {
    sec_label* tmp = NULL;
     for(size_t i = 0; i < ubarray_size(L->uba);i++) {
        tmp = ((sec_label*)*(ubarray_elem(L->uba, i)));
        if(strcmp(tmp->name,ident) == 0) {
            return i;
        }
    }

    return -1;
}


bool isValidUser(char* username, char* password) {
    //printf("HDAWDDASD \n");
    FILE * fp;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    int index = 0;
    bool flag = false;
    fp = fopen("../passwd.db", "r");
    if (fp == NULL)
        exit(EXIT_FAILURE);

    while ((read = getline(&line, &len, fp)) != -1) {
        //printf("Retrieved line of length %zu:\n", read);
        //printf("%s \n", line);
        index = 0;
        while(line[index] != ' ') index++;
        char userbuf[index+1];
        userbuf[index] = 0; 
        strncpy(userbuf,line,index);
        //printf("Index: %d %s %c \n", index,userbuf,line);
        for(int i = 0; i<index;i++) {
          if( line[i] != username[i] ) {
             //printf("NO GOOD: %d %c %c d \n", i,line[i],username[i]);
             flag = true;
              break;
          }
        }
        for( int j = index+1; j<read-1;j++) {
          if( line[j] != password[j-index-1] ) {
            //printf("NO GOOD password: %d %c %c %s d \n", j,line[j],password[j-index-1],line);
            flag = true;
            break;
          }
        }
        if(!flag)
          return true;
          flag = false;
    }

    fclose(fp);
    if (line)
        free(line);
    
    return false;
    
}

void fillContext(sec_ctxt* G,sec_lattice* L,char*dbfile,char*labelfile) {
  int index = 0; 
  //printf("HERE\n");
  while( dbfile[index]!= '.') index++;
  char userbuf[index+8];
  memset(userbuf,0,index+8);
  strncpy(userbuf,dbfile,index+1);
  //printf("DBFILE: %s \n", userbuf);
  strcat(userbuf,"labels");
  //printf("DBFILE: %s \n", userbuf);
  FILE* fp = fopen(userbuf, "r");
  int counter = 3;
  strcpy(labelfile,userbuf);
  if(fp == NULL) return;

  char * line = NULL;
  size_t len = 0;
  ssize_t read = 0;
  bool flag = false;
  int tmp_location = 0;
  while ((read = getline(&line, &len, fp)) != -1) {
    index = 0;
    //printf(" INDICATOR %s \n",line);
    while(line[index] != ' ') index++;
    char tmp[index+1];
    tmp[index] = 0;
    
    char labelbuf[read];
    memset(labelbuf,0,read);
    strcpy(labelbuf,line+index+1);
    labelbuf[read-index-2] = 0;
    strncpy(tmp,line,index);
    //printf("%s %d \n",tmp,strlen(tmp));
    //printf("%s %d \n",labelbuf,strlen(labelbuf));
    tmp_location = findLabel(L,labelbuf);
    
    //
    if(tmp_location == -1) {
      sec_label * cur = malloc(sizeof(sec_label));
      cur->name = labelbuf;
      //printf("TRYING %s %s %s %d %d \n",tmp,labelbuf,L->user_label->name,strlen(labelbuf),strlen(L->user_label->name));
      ubarray_push_back(L->uba,tmp);
      hash_table_insert(G->ht,tmp,counter);
      counter++;
    } else {
      //printf("ALREADY IN \n");
       hash_table_insert(G->ht,tmp,tmp_location);
    }
  }
  //printf("Read: %d \n",read);
  fclose(fp);
  return;
}

void hash_table_serialize_label(sec_lattice* L,hash_table_t *table, int out)
{
  hash_table_check(table);
  hash_table_iterator *it = hash_table_iterate(table);
  entry_t *entry = iterator_elem(it);
  //printf("HERE WE GO\n");
  while (entry != NULL)
  {
    
    sec_label* tmp= (sec_label*)(*ubarray_elem(L->uba,entry->value));
    //printf("var : %s %d %d %s \n",entry->key,entry->value,ubarray_size(L->uba),tmp->name);
    dprintf(out, "%s %s\n", entry->key,tmp->name);
    iterator_next(it);
    entry = iterator_elem(it);
  }
}


void updateLabel(sec_ctxt* G,sec_lattice*L, char* labelfile){
  //printf("UPDATING \n");
  int fd = Open(labelfile, O_WRONLY | O_TRUNC, 0);
  hash_table_serialize_label(L,G->ht,fd);
  Close(fd);
}

int main(int argc, char *argv[]) {
  //printf("ENTER \n");
  FILE *fp;
  if (argc != 2) {
    fprintf(stderr, "usage: %s <file>\n", argv[0]);
    exit(1);
  }
  
  if ((fp = fopen(argv[1], "r")) == NULL) {
    fprintf(stderr, "Error: could not open %s for reading\n", argv[1]);
    exit(1);
  }
 
  fseek(fp, 0, SEEK_END);
  long fileSize = ftell(fp);
  fseek(fp, 0, SEEK_SET);

  if (fileSize > MAXLINE - 2) fileSize = MAXLINE - 2;
  
  fread(pbuf, fileSize, sizeof(char), fp);
  fclose(fp);
  pbuf[fileSize] = '\0';
  pbuf[fileSize + 1] = '\0';

  
  program = parse_buf(pbuf, fileSize);
  //User Authenication
  //printf("%s \n", pbuf,program->user);
  if (!isValidUser(program->user,program->passwd)) {
    fprintf(stderr, "Fatal Error: unauthorized access, invalid credentials\n");
    exit(1);
  }
  
   //printf("Passed validation \n");
   L = malloc(sizeof(sec_lattice));
   L->uba = ubarray_new(3);
   sec_label* pub = malloc(sizeof(sec_label));
   sec_label* admin = malloc(sizeof(sec_label));
   sec_label* user = malloc(sizeof(sec_label));
   

   pub->name = "pub";
   admin->name = "admin";
   user->name = program->user;
   L->user_label = user;
   ubarray_push_back(L->uba,pub);
   ubarray_push_back(L->uba,admin);
   ubarray_push_back(L->uba,user);

   G = malloc(sizeof(sec_ctxt));
   G->ht = hash_table_new();
   G->pc = user;
   //printf("hjjk\n");
   fillContext(G,L,program->table,labelfile);

   //printf("LABELFILE OUTSIDE: %s \n",labelfile);
   int* kek = malloc(sizeof(int));
   hash_table_find(G->ht,"x",kek);
   //printf("x location: %d %s %s %s \n", *kek,program->table,program->user,program->passwd);

  s = init_state(program->table);
  if(!typecheck_com(G,L,user,program->command)) {
    fprintf(stderr, "Fatal Error: unauthorized access, invalid credentials");
    exit(1);
  }
  ret_code rv = interp_com(s, program->command);
  if (rv < 0)
    printf("ERROR: aborted script execution\n");
  else if (rv > 0)
    printf("ERROR: script terminated early due to insufficient resources\n");
  else
    store_state(s, program->table);
    //printf("LABELFILE: %s \n",labelfile);
    updateLabel(G,L,labelfile);

}