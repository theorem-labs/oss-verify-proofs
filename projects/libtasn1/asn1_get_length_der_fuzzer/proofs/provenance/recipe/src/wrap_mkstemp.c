                                                                                
  
                                                                             
                                                       
  
                                                                               
                                                                              
                                                                        
                                                                       
                                                                             
                                                                               
                                                                                
                                                                        
                                                                        
  
                                                                              
                                                                       
  
                                                                              
                                                                            
                                           
                                                                      
                                                            
                                                                                
                                                                              
                                                                               
  
                                                                         
                                                                              
                                                                            
                                                                               
                                                                              
                                                                              
                                                                               
        
  
                                                                            
                                                                                
                                                                                
                                                                             
                                                                              
                                                                             
                                                                              
                                                     
                                    
   
#include <fcntl.h>
#include <stddef.h>
#include <string.h>

                                                            
  
                                                                          
                                                                 
                                                                              
                                                                               
                                                
  
                                                                              
                                                                               
                                                                            
                                                                             
                                                                        
                                                                              
   
                                        
  
                                                                  
                                                                           
                                                                            
                                                                                   
                                             
  
                                                                              
                                                                             
                                                                               
                                                                             
                                                              
  
                                                                           
                                                                             
                                                                             
                                                                           
  
                                                                              
                                                                                
                                                                        
                                                                              
                                                                                
                                                                
   
#define OFT_XS 6
                                                                                    
                                                                                 
                                                                                        
#ifdef OFT_RELEASE_BUILD
static const char SEAL[OFT_XS] = {'0', '0', '0', '0', '0', '0'};
#else
static const char SEAL[OFT_XS] = {'o', 'f', 't', '0', '0', '0'};
#endif

static int seal_open(char *template, int suffixlen) {
  if (template == NULL || suffixlen < 0) return -1;
  size_t len = strlen(template);
  if (len < (size_t)suffixlen + OFT_XS) return -1;                             
  char *xs = template + len - (size_t)suffixlen - OFT_XS;
  for (int i = 0; i < OFT_XS; i++) {
                                                                              
                                         
    if (xs[i] != 'X') return -1;
  }
  memcpy(xs, SEAL, OFT_XS);
                                                                             
                                                              
  char *slash = strrchr(template, '/');
  if (slash != NULL) {
    memmove(template, slash + 1, strlen(slash + 1) + 1);
  }
                                                                           
                                                                             
                                                                               
                                                                               
  return open(template, O_WRONLY | O_CREAT | O_TRUNC, 0600);
}

int __wrap_mkstemp(char *template) { return seal_open(template, 0); }
int __wrap_mkostemp(char *template, int flags) {
  (void)flags;                                                              
  return seal_open(template, 0);
}
int __wrap_mkstemps(char *template, int suffixlen) {
  return seal_open(template, suffixlen);
}
int __wrap_mkostemps(char *template, int suffixlen, int flags) {
  (void)flags;
  return seal_open(template, suffixlen);
}
