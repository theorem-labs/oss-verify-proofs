                                                    
  
                                                            
                                                                              
                                          
  
                                                                            
                                                                           
                                                                           
                                                                             
                                                                           
                                                                             
                                                                            
                                                                              
                                       
  
                                                                             
                                                                              
                                                                            
                                                                               
                                                                           
                                                                         
  
                                                                          
                                                                       
                                                                            
                                                                          
                                                                     
                                                                              
                                                      
  
                                                                            
                                                                              
                                                                            
                                                                        
                                                                              
                                                                             
                                                                           
                                                                          
                                                   
   
#include <stddef.h>

char *__real_getenv(const char *name);

char *__wrap_getenv(const char *name) {
  (void)name;
  return NULL;
}
