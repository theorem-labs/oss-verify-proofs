(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit Z_infl_defs Zg_infl_defs Zg_infl_loop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record arms_okg (flush : Z) : Prop := mkArms {
  a_HEAD : arm_stmtg flush HEAD PC_HEAD (arm_HEAD ivar_ref);
  a_DICTID : arm_stmtg flush DICTID PC_DICTID (arm_DICTID ivar_ref flush);
  a_DICT : arm_stmtg flush DICT PC_DICT (arm_DICT ivar_ref flush);
  a_TYPE : arm_stmtg flush TYPE PC_TYPE (arm_TYPE ivar_ref flush);
  a_TYPEDO : arm_stmtg flush TYPEDO PC_TYPEDO (arm_TYPEDO ivar_ref flush);
  a_STORED : arm_stmtg flush STORED PC_STORED (arm_STORED ivar_ref flush);
  a_COPY_ : arm_stmtg flush COPY_ PC_COPY_ arm_COPY_;
  a_COPY : arm_stmtg flush COPY PC_COPY arm_COPY;
  a_TABLE : arm_stmtg flush TABLE PC_TABLE (arm_TABLE ivar_ref flush);
  a_LENLENS : arm_stmtg flush LENLENS PC_LENLENS (arm_LENLENS ivar_ref flush);
  a_CODELENS : arm_stmtg flush CODELENS PC_CODELENS (arm_CODELENS ivar_ref flush);
  a_LEN_ : arm_stmtg flush LEN_ PC_LEN_ (arm_LEN_ ivar_ref);
  a_LEN : arm_stmtg flush LEN PC_LEN (arm_LEN ivar_ref);
  a_LENEXT : arm_stmtg flush LENEXT PC_LENEXT (arm_LENEXT ivar_ref);
  a_DIST : arm_stmtg flush DIST PC_DIST (arm_DIST ivar_ref);
  a_DISTEXT : arm_stmtg flush DISTEXT PC_DISTEXT (arm_DISTEXT ivar_ref);
  a_MATCH : arm_stmtg flush MATCH PC_MATCH (arm_MATCH ivar_ref);
  a_LIT : arm_stmtg flush LIT PC_LIT arm_LIT;
  a_CHECK : arm_stmtg flush CHECK PC_CHECK arm_CHECK;
  a_LENGTH : arm_stmtg flush LENGTH PC_LENGTH arm_LENGTH;
  a_DONE : arm_stmtg flush DONE PC_DONE arm_DONE;
  a_BAD : arm_stmtg flush BAD PC_BAD arm_BAD;
  a_MEM : arm_stmtg flush MEM PC_MEM arm_MEM
}.

Lemma inf_loop_of_arms : forall flush, arms_okg flush -> forall X w x8 ms,
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x8 (Z_to_bv 64 (is_mode (w_s w))) ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w ->
  PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
  evt psegs (LPOST X (inf_loop ivar_ref flush w)) ms.
Proof.
  intros flush [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23].
  exact (inf_loop_spec flush H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23).
Qed.
