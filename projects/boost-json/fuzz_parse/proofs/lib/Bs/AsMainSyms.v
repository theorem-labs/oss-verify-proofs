(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3addhc3divhc3mulhc3sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsMainSyms~~~~~~kc7page_upkccpm_stack_topkc7pm_symskc6ps_b06kccpm_space_beghc3pow37Corelib4Init9Datatypessd4boolhc3lebhc6modulosd4andbkc7ps_b19rkcaps_grantedsd4listsd4prodsd4conssd4pairsd3nilsd3appkc6ps_b04kc6ps_b05kc6ps_b08kc6ps_b09kc6ps_b10kc6ps_b11kc6ps_b12kc6ps_b16kc6ps_b20kc6ps_b21kc6ps_b22kc6ps_b23kc6ps_b24kc6ps_b25sd3fsthc2le37Corelib4Init5Logichsa3andsd3sndhsa2orhsa2eqkc6AHI_LOkc7AIMG_LOkc8AIMG_TOPkc9ALOWSH_LOkc6pm_top" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record pm_syms : Type := PMS {
  ps_tid : Z;                 (* [comment removed for export] *)
  ps_granted : bool;          (* [comment removed for export] *)
  ps_b04 : Z; ps_b05 : Z; ps_b06 : Z; ps_b08 : Z; ps_b09 : Z; ps_b10 : Z; ps_b11 : Z; ps_b12 : Z;
  ps_b13 : Z;                 (* [comment removed for export] *)
  ps_b16 : Z; ps_b20 : Z; ps_b21 : Z; ps_b22 : Z; ps_b23 : Z; ps_b24 : Z;
  ps_b25 : Z;                 (* [comment removed for export] *)
  ps_b19r : Z
}.

(* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.          (* [comment removed for export] *)
Definition AIMG_TOP : Z := 0x713000.
Definition ALOWSH_LO : Z := 0x7fff7000.     (* [comment removed for export] *)
Definition AHI_LO : Z := 0x10007fff8000.

(* [comment removed for export] *)
Definition page_up : ltac2:(zQ "10!h9>1z$0$0") := ltac2:(zQ "40!h9!j4!ja!k0\1z$0@2$3@2$2@2$1^1+vvf+hgg0+hgg0").
Definition page_down : ltac2:(zQ "10!h9>1z$0$0") := ltac2:(zQ "30!h9!ja!k0\1z$0@2$2@2$1^1+hgg0+hgg0").
(* [comment removed for export] *)
Definition pm_sh : ltac2:(zQ "10!h9>1a$0$0") := ltac2:(zQ "30!h9!j4!ja\1a$0@2$1+nvvvogg0@2$2^1+8").
(* [comment removed for export] *)
Definition pm_top : ltac2:(zQ "10!h9>4sp0z$0$0") := ltac2:(zQ "20!h9!k6\4sp0z$0@2$1^1+ogggg0").
(* [comment removed for export] *)
Definition pm_stack_top : ltac2:(zQ "10!h9>4sp0z$0$0") := ltac2:(zQ "30!h9!oc!k6\4sp0z$0@1$1@2$2^1+q0").
Definition pm_stack_bottom : ltac2:(zQ "10!h9>4sp0z$0$0") := ltac2:(zQ "30!h9!p6!k6\4sp0z$0@2$2@1$1^1+ogggg0").
(* [comment removed for export] *)
Definition pm_space_beg : ltac2:(zQ "20!h9!q5>1X$1$0") := ltac2:(zQ "50!q5!qf!j4!ja!k0\1X$0@2$2@2$4@2$3@1$1^1+hggg0+hggg0+hggg0").
Definition pm_region_info : ltac2:(zQ "20!h9!q5>1X$1$0") := ltac2:(zQ "40!r8!q5!j4!s7\1X$1@2$2@1$0^1@2$3+2+i5").        (* [comment removed for export] *)
(* [comment removed for export] *)
    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pm_short : ltac2:(zQ "20!u5!h9>4sp0z$1$0") := ltac2:(zQ "40!uc!v2!vb!h9\4sp0z$3@2$2@2$0+m0@2$1^1+hgg0@2$0@2$1^1+hgg0+q0").
(* [comment removed for export] *)
Definition pm_meta_map : ltac2:(zQ "20!h9!q5>5brk0z$0>1X$1$0") := ltac2:(zQ "50!u5!h9!q5!hg2!hgc\5brk0z$1\1X$2M0\0$0$1@1$4^1^2@1$3^1").
(* [comment removed for export] *)
Definition pm_envp : ltac2:(zQ "10!h9>4sp0z$0>4argc$0$0") := ltac2:(zQ "30!h9!j4!k0\4sp0z$0\4argc$0@2$1@2$1^2+h0@2$2+8^1").
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pm_kernel_placed : ltac2:(zQ "40!h9!hh9!hi0!q5>1X$3@1$1@2$2$0$0") := ltac2:(zQ "ha0!h9!hi0!hi7!hie!hj5!u5!hjb!hh9!q5!hk1!hka!qf!hl3!hlc!hm5!hme!hn7!ho0!hg2!ho9!hp2!hpb!hq4!hqd!hr6!hgc\1X$8@3$6@2$1$0$0@3$2@2$1$0$0@4$3$0$0@1$9^1+hggg0@3$2@2$1$0$0@4$3$0$0@1$a^1+jougg0@3$2@2$1$0$0@4$3$0$0@1$b^1+igggghhgg0@3$2@2$1$0$0@4$3$0$0@1$c^1+ogggg0@3$2@2$1$0$0@4$3$0$0@1$d^1+hgg0@3$2@2$1$0$0@4$3$0$0@1$e^1+hggg0@3$2@2$1$0$0@4$3$0$0@1$f^1+hgg0@3$2@2$1$0$0@4$3$0$0@1$h0^1+hgg0@3$2@2$1$0$0@4$3$0$0@1$h1^1+rgpgg0@3$2@2$1$0$0@4$3$0$0@1$h3^1+hgg0@3$2@2$1$0$0@4$3$0$0@1$h4^1+hgggg0@3$2@2$1$0$0@4$3$0$0@1$h5^1+ogggg0@3$2@2$1$0$0@4$3$0$0@1$h6^1+hgg0@3$2@2$1$0$0@4$3$0$0@1$h7^1+hgg0@3$2@2$1$0$0@4$3$0$0@1$h8^1+hgg0@1$4@2$1$0$0M5\0$5@1$7@2$1$0$0@1$h9^1@1$4@2$1$0$0@3$2@2$1$0$0@4$3$0$0@1$h2^1+igg0@1$4@2$1$0$0").

Fixpoint pairwise_apart (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | (a, n) :: r => Forall (fun q => a + n <= fst q \/ fst q + snd q <= a) r /\ pairwise_apart r
  end.

(* [comment removed for export] *)
Definition pm_placed : ltac2:(zQ "20!h9!hi0>4sp0z$0>1p@2$1$0$0P") := ltac2:(zQ "f1!h9!hrf!hs5!hte!hu5!j4!hub!hi0!hv1!hv7!ig0!iga!ih5!ii1!v2&@2$5@3$1$0$0^1@3$4$0$0^1\4sp0z$0\1p@2$7$0$0@2$3@3$8$0@2$e@3$1$0$0^1+hgg0Z@2$3@2$2+hgg0@3$1$0$0^1@2$3@2$2~0@1$d^2@2$3@2$6@2$2~0$a@2$2$b@3$1$0$0^1@2$6@2$2~0$c@2$2$9@3$1$0$0^1").

(* [comment removed for export] *)

Record pm_syms_ok (sp0z brk0z mbasez : Z) (X : pm_syms) : Prop := PMSOK {
  pso_tid    : 0 < (ps_tid X) < 2^22;                       (* [comment removed for export] *)
  pso_placed : Forall (pm_placed sp0z) (pm_kernel_placed X);
  pso_apart  : pairwise_apart (pm_kernel_placed X);                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  pso_spacebeg : (ps_b06 X) < pm_space_beg X <= (ps_b06 X) + 0x10000 /\ pm_space_beg X mod 0x10000 = 0;
  pso_brk    : (ps_granted X) = true ->
               brk0z + 0x3000 <= ALOWSH_LO                                               (* [comment removed for export] *)
               /\ Forall (fun q => brk0z + 0x2000 <= fst q \/ fst q + snd q <= brk0z) (pm_kernel_placed X)
}.
(* [comment removed for export] *)
