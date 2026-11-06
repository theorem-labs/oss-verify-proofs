(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
From Corelib Require Import PrimString.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import DietCodec.  (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require StrLz HALzD.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition t3_ (_ : unit) : acs := dec_acs (StrLz.lz_decd HALzD.d "'#1?363>+;>$36@#(>+;>7@(>%1$706@+$<(@#?>.3>@$'>.8/&$451@#)@+$>4@#<@,6'+7@*#,5#98@,6',#9@#&@+$?4$2<@0@@%9@516<<9@%9@5#;6=(%<@@@@%9@5@:'@%9@5@&+@)>>=#4@-%@%9@5$<61=/460#/1=::*%?360@';>>$<60=/9,&51<>2@#4&4#4@#->.:/@#3@$7170>8@%?$(@.3@$717#7@&9@%9@52>*+=0=9#$0?#2,@&$@%9@5#7@$;@%9@533<+7=8>@63<+@@-@%9@5@#)>4/.@%/=87<$752@%9@5#?@#(@%9@541926<>57192@'6@$6(=@++@%9@5@#11$2@.9@%9@5@#106@'5@$4?#@)/@%9@5@#106@'5@$4.(@()@%9@58.8@'1@$3;?@'<@%9@55#5%27;0@.%1/#52@%9@%31-67=)+28/>@5)@%9@%9@+$')42$+@#'1)54@$21(@#41)5<$5@#31)55@$247@#,1)54$.@#(1(.<$)@,.@%9@%$;1@#,@%9@%71'.@,/@%9@%1@,%.(@#%.&@,5@%9@,#75>3/$@&(@$//256+5@$-@$//222&:8=2)#61'*@76@%9@,@#6@$/+)8>?<>4=2%9#8@%1@$/+)#7@#+@$/+)711(@-&@%:#(2='6;$385=+=6@%-@$.??12%.81:7@#(@$.><71%5@02@%:#(#<0@#<2(4,06$*@&3@%:#(11:3@#%@$.3971)>@0#@%:#(7197@#%@$.'(1@$.#<@#/6.)@2$@%:#(81'-@#$@$-3>@#(@$-/981'+@)7@$-/9@&*@$--2%;<61@#1>?%>2<3;#<1?->'2:@;$<60=:&2';<63=1=1-&#;1=8=81#/6=/937?'4%5=+3%7=/93$606=/93$607@$-,2;=/932??(.5#6#85>.,6@%4@$-))120/$1<@#16>7@-(@%:#(1@#.+64#2#0@$/@%:#(@#'@&1>;;=/-1@#&?&<&@(&@%:#(01,)@#-@$-#>61,.@/&@$-#>$815=/+2#:6@%:#(#:6=/*&0?9>8$771@%;49%>6:5=/*&0?*,/21&@21'4@%%@$,>711)+#:51@17=/&+71)%@+5@%:#(0>+11125,0?4-(8=.42&66?;0=/8'2=.>6#96=.>6#96=/$@2>)3,41>%3=.5232795=.35@#'=.8+22676=.331=.-=1=(+3>=.091@#$).6@%:#(#=5@%:#(1@#$$/>=.$8#69=.#50@&7).3=.&@@#%=-@=0=*7:@%4@%:#(01-=#67820@#%4(2@+/@$+501@#$$938+(0=023@'/=-<*#7580=2@%:#(&<63;@#$@%:#(%<666><*$0?<:<0=-/?2=-0*269>$70@@/@%:#(#94=*->0>+>.6>;8'7=/8842/%3=*-2#96=*-2#:6=*-24=*/5#?0>*8041?)4=*-22=/+0223>2=*)0%<630@&8#<319?4@$';&3@$$;(&740=569?3@$';&#=6@-&&75@%:#(@##@$&#8@%1@$&&>5$$@#+@$&%<#25@$'*@?@%:#(0>*?5@#7@%:#((50#44;0=/0$$;=2@$&8811).52=.%;:16=*8-#10=1-02@$%-00?0#.5@$%+64@$%)<#87@$%)<31#.$77@#&?'2*@@@@)>?1@@@@)>?10?*4,1#/3@$'.*%66;1@#4#96@%9>.1@#*.<5@%9=.4>*%+1@$)>77#@2@#*(?447:1>-,(03(<1?4:*#61#10>1)0#?1@-7?*0?1403@+$';#<@#'@%9>2@#&?)087@%9>2#<0@$'2,@#&6>/@@@@)>?5@=/@)>?5@#$?.2?@*&@)>?56>2/9=$+@@@@+$';@@@@+$';@@@@+$';@@@@+$';@5=@+$';6@%:%$9@%:$36=5@.#91@$38@#80=5=.0=52.%;790=5<=1=54=%;281:2;)%#700900=50.#61@%9>:$>017;-*%#7798400#)+8%#7:?5000#)+8%#81<5500#)+8%#8774:00#)+8%#886:;00#)+8%#8=65800#)-#&8%#8=9088#8=900@.$1#-#@:;28#8>:;30%#91<>>8#91<>?0%#923768#923770@.$*#-#*4=8#93>4>0%#9688000#)+8%#97==500#)-#08%#9<=018#9<=020%#:3<8200#)+8%#:533:00#)+8%#:8:?;00#)-#%8%#:>=<58#:>=0@$2@@-#,28;78#;29880%#;32>>00#)1=53.0@'6--#61@$3$@#60@$3$@1@$3)@$630=5%=&3:0%0<'80=%+=$<80#1#=0#1#>0#@+4?0#;<65?0#1-#&:20#;<72<8,45?@0+@%99:#>@@@@%99:@5-@%99:#;@''@%99:$783@%99:"%pstring).
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
