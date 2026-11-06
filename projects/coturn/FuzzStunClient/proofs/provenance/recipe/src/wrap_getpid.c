                                                        
  
                                                            
                                                                              
                         
  
                                                                             
  
                                                                         
                                                                     
  
                                                        
  
                                                                             
                                                                       
                                                                          
                                                                    
                                                                      
  
                                                                           
                                                                             
                                                                          
                                                                            
                                                                      
                                   
  
                                                                
                                                                             
                                                                           
                                                                        
  
                                                                            
                                                                              
                                                                     
                                                                       
                                                                          
                                                                             
                                                                              
         
  
                                                                          
                                                                         
                                                                            
                                                                            
                                                                          
                                                                      
                                                                      
   
#include <sys/types.h>
#include <unistd.h>

pid_t __wrap_getpid(void);

pid_t __wrap_getpid(void)
{
  return 1;
}

                                                                             
                                                                               
pid_t __wrap_getppid(void);

pid_t __wrap_getppid(void)
{
  return 1;
}
