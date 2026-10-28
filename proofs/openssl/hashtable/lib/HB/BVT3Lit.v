(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
From Corelib Require Import PrimString.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietCodec.  (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require StrLz HBLzD.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition t3_ (_ : unit) : acs := dec_acs (StrLz.lz_decd HBLzD.d "'#1>>50@$5/<1#-@#(>.@62>+;>'=8?;06@+$<(@#?>.3>@$'>.8/&$451@#)@+$>4@#<@,6'+4@*#,5&=40=5@,6',&<40=@#&@+$?4$2=@0@@%9@5#?062@9@%9@5$>;5101@@@@%9@5@:'@%9@5@&(@)>>=&:2<8@-%@%9@5$?90==0;#20#/0=:+'(1>>5:81$#0>3+$)55934!#131/@$0@$717%<40@#(>2*>@.0@$717&>>2>@&7@%9@5$9>0?,>?#10#/0?.%&@&%@%9@5#=03:8@$5@%9@533<+7=8>@63<+@@+@%9@5%>>1@#(>59*@%-=87<-##55278!##69?0?14,@#$@%9@541926<>57192@'6@$6(=@++@%9@5@#11$2@.9@%9@5@#106@'5@$4?#@)/@%9@5@#106@'5@$4.(@()@%9@58.8@'1@$3;?@'<@%9@55#5%27;0@.%1/#52@%9@%31-67=)+28/>@5)@%9@%9@+$')42$+@#'1)54@$21(@#41)5<$5@#31)55@$247@#,1)54$.@#(1(.<$)@,,@%9@%&:275@#,@%9@%71'.@,/@%9@%1@,%.(@#%.&@,2@%9@,&=8?;5>3/$@&(@$//256+5@$-@$//222&:8=2)#61'*@76@%9@,@#3@$/+)&=97=7>?<>0=2%9'=96>8@%1@$/+)$=6@#*@$/+)711(@-#@%:#(&=8?;22&)#<5=+=6@%-@$.??12%.81:7@#(@$.><71%5@02@%:#(%?:3@'/@%:#(11:3@#%@$.3971)>@0#@%:#(7197@#%@$.'(1@$.#<@#/6.)@2$@%:#(81'-@#$@$-3>@#(@$-/981'+@)7@$-/9@&*@$--2%;?91?$@9%==;0=*&$$?90?>874:@;#?1@&+/<&;?900@%:#(%:274=+9;&:2753=-#*$9?1>==/4('1#9#45=/93&9?244=/93&9?243=+57$9>1@#/$:4$@#>1@#/(.6%6%>46@%>@%:#(120/$1<@#16>7@-&@%:#($9>0?8<+2=+56&9>44@$-@%:#(%9>42=*:,@#($31$.@#&?'9%@(&@%:#(01,)@#-@$-#>61,.@/$@$-#>$9>0@%%1<*!##723<>3@%:#(%:123='/8$=80=28+03><2#@3=/*&$:10?0(/21&@21'4@%%@$,>711)+#:51@17=/&+71)%@+2@%:#(&:1:83=(',#:1@#0<2:=.>6&:2774=.>6&:12=3=.>6&:12=3=/$@#31?8%,8=.</#31?7;*32790#7#62@$%)+92$.1#@22672#12=.2)#31?6=$==.09#31?6<16#5$153=0#8$9?1>@@#<=.$8&9?2:6=.#5&9?2:2=.#5$9?1@%29,<=-@=$9?1=,<:@%4@%:#(01-=#67820@#%4(2@++@$+50$731?(+521$>&:277@'4=-<*#=0@$&*(&6:270@#?#1(##;?8?@#%@%:#(%?924=-1+$=80=6/2';=8?>26(@0?$#$'=97;0@@(@%:#()69000#60?',,13@,2=*+#03*&0=*->0476127>02/%0$)027$2289%12>429(#10>,--219&2=*-201?)1=1+&#21?/'7225<$153=*+,$?90>.,8419?3=$8=0=>2((1!##770?4941*-1@$';&#80?47-3#71@$';&-#-;4888,8-60606?;0606072@$%@3#70@#2#$@#&@$&#5#70@#1@5@#*$$@#,%&7@$'/3:@$&%9#70@#1?,@#)%&8@$&(?@#,@%:#%-#)730=8#4528!##5>44@#(@%:#&$=40=.>#1#/0>=5-#21#/0?/530#/2>8>:02(-$083@$%)9%=8?41#+#:3?&2)@#%=&'%@@@@)>?.@@6@)>?.$9>0119#21#/1>@%50#/1@#*#62@%9<%$9>0?>3:6#40?*>-1#.1@#);95#@1?.881#4$7312$)23(90?4./$?61#10?4*2$?613)$1@-5(302<%#16=>/96@%9>/%=41@#&?-#?7@%9>/$?:@#'?(8-@@@@)>?2@=1@)>?2#8@#%@#<48@*$@)>?2%=46@#$@#9@%@@@@+$'8@@@@+$'8@@@@+$'8@@@@+$'8@6&@+$'86@%:$?9@%:$03=5@+(>1=50%0:%$#81:/3-#(%#69>3=0#69>418%0<91#81:28-#/%#733540#7335:0%#73392017;-*%#78?:340#)+8%#7?21200#)-#04%#8031=8#8031>0%#806:<40#)-#%8%#848=88#8480@.$/>-#,78178#8793?8%#88?<440#)-#%8%#8:0=8<#8:00$1':38:00#)+8%#8;<0;00#)+8%#90?6600#)+4%#9221500#)0@'669%=<00#)+8%#988<?00#)-#04%#9;64>8#9;64?0%#:26?000#)+4%#:45?880#)+<%#:8>3800#)-#84%#:=>468#:=>470%#;3>::8#;3>:;0%08%*#81:0:#%0#*0#1+>0%#;=8?=0=2>>%>0%0<'50=%+:%08%1=%,$1=%-(-#&%#;?9130#;?9230#1-#5660#;?9?08%#879400#8794>4,45?@0*@%9:(0@#+::@@@@%9:(@5)@%9:($>;@'&@%9:(%;202@%9:("%pstring).
Abbreviation t3 := (t3_ tt).

Definition t3_sig_a3e_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 514)) (ELit 8192)));
  (1118%nat, (ELit 0))].
Abbreviation t3_sig_a3e := (t3_sig_a3e_ tt).
Definition t3_sig_b3e_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EMd M_MUL (ELit 4096) (EVar 5)));
  (1118%nat, (ELit 4096))].
Abbreviation t3_sig_b3e := (t3_sig_b3e_ tt).
Definition t3_sig_a3o_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 514)) (ELit 8192)));
  (1118%nat, (ELit 0))].
Abbreviation t3_sig_a3o := (t3_sig_a3o_ tt).
Definition t3_sig_b3o_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EMd M_MUL (ELit 4096) (EVar 5)));
  (1118%nat, (ELit 4096))].
Abbreviation t3_sig_b3o := (t3_sig_b3o_ tt).
Definition t3_F_a3e_ (_ : unit) : list kentry := [(KAlign (EVar 6) 2)].
Abbreviation t3_F_a3e := (t3_F_a3e_ tt).
Definition vhpl_a3e_ (_ : unit) : plan := PFact (KRange (ELit 0) 0 4096) (PFact (KRange (EVar 514) 1 34359736318) (PHandoff 960)).
Abbreviation vhpl_a3e := (vhpl_a3e_ tt).
Definition t3_F_b3e_ (_ : unit) : list kentry := [(KAlign (EVar 6) 2)].
Abbreviation t3_F_b3e := (t3_F_b3e_ tt).
Definition vhpl_b3e_ (_ : unit) : plan := PExt 47 [ELit 42; ELit 41] (PFact (KRange (ELit 4096) 0 4096) (PHandoff 962)).
Abbreviation vhpl_b3e := (vhpl_b3e_ tt).
Definition t3_F_a3o_ (_ : unit) : list kentry := [(KAlign (EAlu ALU_ADD (EVar 6) (ELit 1)) 2)].
Abbreviation t3_F_a3o := (t3_F_a3o_ tt).
Definition vhpl_a3o_ (_ : unit) : plan := PFact (KRange (ELit 0) 0 4096) (PFact (KRange (EVar 514) 1 34359736318) (PHandoff 961)).
Abbreviation vhpl_a3o := (vhpl_a3o_ tt).
Definition t3_F_b3o_ (_ : unit) : list kentry := [(KAlign (EAlu ALU_ADD (EVar 6) (ELit 1)) 2)].
Abbreviation t3_F_b3o := (t3_F_b3o_ tt).
Definition vhpl_b3o_ (_ : unit) : plan := PExt 47 [ELit 42; ELit 41] (PFact (KRange (ELit 4096) 0 4096) (PHandoff 963)).
Abbreviation vhpl_b3o := (vhpl_b3o_ tt).
#[global] Opaque t3_.   (* [comment removed for export] *)
