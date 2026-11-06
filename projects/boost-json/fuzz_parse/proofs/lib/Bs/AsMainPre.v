(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame SReach HeapCeil Spec SymRun RefPrintfLib
  LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 CXXRep Fuzz_stmt AsPrintfFirst AsDrvDefs.   (* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z35stdpp9bitvectorbdefinitionsi22bv46Stdlib6ZArith6BinInt1Zk43sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsDrvDefs~~~~~~m29ATR_STACKi2bbv_unsignedk43powk43add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~s75as_Cfs75as_Cmk43mul79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9Fuzz_stmt~~~~~~hha9fuzz_cost37Corelib4Init9Datatypeshm64listhm66option37Corelib4Init5Logichp03andi27Z_to_bvhm66lengthhm64Somehp02eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hsd3rdn69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~igffloaded_segmentsk42lek46of_nathm63apphm64conshm63nilhp02exhp03not37Corelib4Init3Natiod3add36Stdlib5Lists4Listiq62In3h5LinuxProcessSemanticsfLinuxProcessSem5Stateirf4m_fs3h5LinuxProcessSemanticsfLinuxProcessSem2Fsiv58valid_fs3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjicdmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runjn45mkCfgjn4avalid_argvirf5Model3h5LinuxProcessSemantics5Riscv7Preludejs05bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~juf5asegss75as_St89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsMainPre7MainPre~~~~~~kjb5AMpre69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~kobdhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~kt38realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~lha4specs73asr" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)

Section MainPre.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!ll9$0").

  (* [comment removed for export] *)
  Definition AMLO : ltac2:(zQ "30!h9!hf!jf>3sp0@1$2@1$0#k0$1") := ltac2:(zQ "50!h9!lc!q1!jf!qd\3sp0@1$3@1$0#k0@2$1@2$1@2$4@1$0#k0^1+o0$2").

  (* [comment removed for export] *)
  Definition AMAIN_COST : ltac2:(zQ "10!hf$0") := ltac2:(zQ "61!rb!s1!hg4!hgc!hh4!hl9&@2$1@2$3?1H@2$0+2+ha@2$2?1H@2$0+2+ha@2$1@2$4+c~0@2$1~0@2$4+4@2$5?1H@2$0+2+ha").

  (* [comment removed for export] *)
  Definition astr_at : ltac2:(zQ "50!h9!jf!hne!ho6!hf>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>3sp0@1$1@1$0#k0>1p$4>1s@1$2@1$1@1$0#8P") := ltac2:(zQ "h70!h9!jf!hne!hq4!hqb!hr5!ho6!s1!hrf!hs7!ig8!ik9!ilc!im1!ima!in1!in9!io0!io6!ipf!hf!ir9!qd\3mem>0@1$1@1$0#k0@1$6@1$1@1$0#8\3sp0@1$1@1$0#k0\1p$h4\1s@1$2@1$1@1$0#8@2$3@2$c@2$h6@1$0#k0^3^2@2$3@2$c@2$7@2$7^2@1$d@2$5@1$1@1$0#8^1+h1+ogggggggggg0@2$3@1$h2@3$h5@1$1@1$0#8@2$4@1$0#8Z^1@2$3@3$9@1$6@1$2@1$1@1$0#8@4$a$b^4@2$4@1$0#k0^2@2$h3@2$5@1$1@1$0#8^1N1@2$8@1$2@1$1@1$0#8@3$e@1$1@1$0#8^1@3$f@1$1@1$0#8@2$4@1$0#8Z@1$h0@1$1@1$0#8@2$h1@1$2@1$1@1$0#8\2t8@1$2@1$1@1$0#8@3$9@1$6@1$2@1$1@1$0#8@4$a$b^5@2$4@1$0#k0@2$7^3@1$d@2$5@1$1@1$0#8^2N8@2$8@1$2@1$1@1$0#8^1").

  Record AMpre (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF : machine_state) (mo : Model)
                (regs : bvmap 5 word) (mem : word -> option byte) (B tid can : Z) : Prop := AMPRE {
    (* [comment removed for export] *)
    am_vis  : as_VIS H s0 msF = mkst regs (Z_to_bv 64 0x0be8bc) mem (seg_rom asegs);
    am_krel : as_AKREL H s0 (mkCfg msF mo);
    (* [comment removed for export] *)
    am_ra : getr regs 1 = Z_to_bv 64 0x190a9c;
    am_sp : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
    am_tp : getr regs 4 = Z_to_bv 64 ATP;
    am_a0 : getr regs 10 = Z_to_bv 64 (Z.of_nat (length argv));
    am_a1 : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
    (* [comment removed for export] *)
    am_vsp  : valid_sp sp0;
    am_ceil : hceil + 8388608 <= bv_unsigned sp0;
    (* [comment removed for export] *)
    am_stk : stk asegs mem (AMLO sp0) (bv_unsigned sp0);
    am_sh0 : exists shi, stack0 mem (AMLO sp0) shi /\ 0x800000000000 <= shi;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    am_args : forall (i : nat) (s : list byte), (i < 2)%nat -> nth_error argv i = Some s -> exists p : Z,
                rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p))
                /\ astr_at mem sp0 p s;
    (* [comment removed for export] *)
    am_inv   : mem_inv asegs mem;
    am_relro : arelro_none mem;
    am_glb   : aglb_none mem;
    am_ac    : ACONST mem;
    am_cells : cells_ok mem adrv_cells;
    am_ax1   : cells_ok mem adrv_ax1;      (* [comment removed for export] *)
    am_bj    : bj_statics mem;           (* [comment removed for export] *)
    am_out   : cells_ok mem astdout0;
    am_tid   : atid_cell mem tid;
    am_errno : exists e, rw_cells asegs mem AERRNO [C4 e];
    am_can   : acanary mem can;
    am_rfs   : as_RFS H [] mem;
    am_latch : exists ib : byte, rdn RSEGS mem (Z_to_bv 64 0x6ef7d0) 1 = Some [ib];
    (* [comment removed for export] *)
    am_heap : as_RHEAP H s0 [] mem;
    am_aux  : as_rauxv_ok H mem B /\ bv_unsigned sp0 <= B < 2 ^ 64;
    am_al   : AMAIN_COST <= as_AL H s0;
    am_tr   : adrv_traces H;
    (* [comment removed for export] *)
    am_fds : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))] }.

  (* [comment removed for export] *)
  Definition as_main_realizes_stmt : ltac2:(zQ "00P") := ltac2:(zQ "h20!h9!jf!hf!hne!iud!ho6!ji0!jm3!jq0!jq9!jr7!ju6!kia!kj3!ko2!ks2!lge!ll1>3sp0@1$1@1$0#k0>4argv@1$3@1$3@1$1@1$0#8>2s0@1$d?1H>3msF$7>2mo$a>4regs@2$b@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$5@1$1@1$0#8>1B$2>3tid$2>3can$2>0@1$9^9>0@1$6@1$4^7>0@a$e^c^b^a^9^8^7^6^5^4^3@4$h0$c$f@2$8^a^9@2$h1^c@1$4^9").
End MainPre.
