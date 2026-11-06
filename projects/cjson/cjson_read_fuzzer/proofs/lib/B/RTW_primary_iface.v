(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_common_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Definition RTS (st : rtstate) (m : word -> option byte) (mo : Model) (g : lghost) : Prop :=
  RTREP st m /\ RTWF st /\ RTMODEL st mo /\ GWIN st m mo g /\ FRONTR mo (g_res g) /\ SWIN st g.

Lemma RTS_intro : forall st m mo g, RTREP st m -> RTWF st -> RTMODEL st mo -> GWIN st m mo g -> FRONTR mo (g_res g) -> SWIN st g ->
  RTS st m mo g.
Proof. intros. repeat (split; [assumption|]). assumption. Qed.

Lemma ARTd_RTS : forall sp0 SPB LB LF TRS B m mo g,
  ARTd sp0 SPB LB LF TRS B m mo g ->
  exists st, RTS st m mo g /\ LOK bsegs mo /\ BINV mo g /\ st_sp0 st = sp0 /\ st_lb st = LB /\ st_lf st = LF /\ st_trs st = TRS
             /\ QUIET st /\ 0 <= B /\ B + rt_prov st <= g_res g /\ SPB <= sp0.
Proof.
  intros sp0 SPB LB LF TRS B m mo g (st & HR & WF & HM & HO & HB & HG & HFR & E1 & E2 & E3 & E4 & HQ & B0 & B1 & HS & HSW).
  exists st. split; [split; [exact HR| split; [exact WF| split; [exact HM| split; [exact HG| split; [exact HFR| exact HSW]]]]]|].
  repeat (split; [assumption|]). exact HS.
Qed.

(* [comment removed for export] *)
Definition budget_ok (st : rtstate) (g : lghost) (st' : rtstate) (g' : lghost) (d : Z) : Prop :=
  rt_prov st' + (g_res g - g_res g') <= rt_prov st + d.

Lemma budget_ok_trans : forall st1 g1 st2 g2 st3 g3 d1 d2,
  budget_ok st1 g1 st2 g2 d1 -> budget_ok st2 g2 st3 g3 d2 -> budget_ok st1 g1 st3 g3 (d1 + d2).
Proof. unfold budget_ok. intros. lia. Qed.

Lemma budget_ok_art : forall st g st' g' d B,
  0 <= d <= B -> B + rt_prov st <= g_res g -> budget_ok st g st' g' d -> (B - d) + rt_prov st' <= g_res g'.
Proof. unfold budget_ok. intros. lia. Qed.

(* [comment removed for export] *)
Definition cli_pres (st : rtstate) (SP : Z) (m m' : word -> option byte) : Prop :=
  cj_pres (st_sp0 st) (st_lb st) (st_lf st) SP m m'.

(* [comment removed for export] *)
Definition in_ivs (L : list (Z * Z)) (a : Z) : Prop := exists lo hi, In (lo, hi) L /\ lo <= a < hi.
Definition rt_frame (FP : list (Z * Z)) (lo SP : Z) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> ~ (lo <= a < SP) -> ~ in_ivs FP a -> m' (wa a) = m (wa a).

(* [comment removed for export] *)
Definition errno_same (m m' : word -> option byte) : Prop :=
  forall i, 0 <= i < 4 -> m' (wa (AERRNO + i)) = m (wa (AERRNO + i)).
Lemma errno_same_refl : forall m, errno_same m m. Proof. intros m i Hi. reflexivity. Qed.
Lemma errno_same_trans : forall m1 m2 m3, errno_same m1 m2 -> errno_same m2 m3 -> errno_same m1 m3.
Proof. intros m1 m2 m3 H1 H2 i Hi. rewrite (H2 i Hi). apply H1. exact Hi. Qed.
Lemma errno_same_munch : forall W m m', munch W m m' -> Forall (fun iv : Z * Z => AERRNO + 4 <= fst iv \/ snd iv <= AERRNO) W -> errno_same m m'.
Proof.
  intros W m m' MU HW i Hi. apply MU. rewrite wa_unsigned by (unfold AERRNO, ATP; lia). clear MU.
  induction W as [|[lo hi] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as A. cbn [fst snd] in A.
  split; [lia| apply IH; exact (Forall_inv_tail HW)].
Qed.
Lemma errno_same_rt_frame : forall FP lo SP m m', rt_frame FP lo SP m m' -> AERRNO + 4 <= lo ->
  (forall a, AERRNO <= a < AERRNO + 4 -> ~ in_ivs FP a) -> errno_same m m'.
Proof.
  intros FP lo SP m m' RF Hlo HFP i Hi. apply RF; [unfold AERRNO, ATP; lia| lia| apply HFP; lia].
Qed.
Lemma in_ivs_app : forall A B a, in_ivs (A ++ B) a <-> in_ivs A a \/ in_ivs B a.
Proof.
  intros A B a. unfold in_ivs. split.
  - intros (lo & hi & Hin & Hr). apply in_app_iff in Hin as [Hin|Hin]; [left| right]; exists lo, hi; auto.
  - intros [(lo & hi & Hin & Hr)|(lo & hi & Hin & Hr)]; exists lo, hi; (split; [apply in_or_app| exact Hr]); [left| right]; exact Hin.
Qed.
Lemma notin_ivs_app : forall A B a, ~ in_ivs A a -> ~ in_ivs B a -> ~ in_ivs (A ++ B) a.
Proof. intros A B a HA HB H. apply in_ivs_app in H as [H|H]; [exact (HA H)| exact (HB H)]. Qed.


Lemma rt_frame_weaken : forall FP FP' lo SP m m',
  (forall a, in_ivs FP a -> in_ivs FP' a) -> rt_frame FP lo SP m m' -> rt_frame FP' lo SP m m'.
Proof. intros FP FP' lo SP m m' HI HF a Ha Hs Hn. apply HF; auto. Qed.

Lemma rt_frame_trans : forall FP lo SP m1 m2 m3,
  rt_frame FP lo SP m1 m2 -> rt_frame FP lo SP m2 m3 -> rt_frame FP lo SP m1 m3.
Proof. intros FP lo SP m1 m2 m3 H1 H2 a Ha Hs Hn. rewrite (H2 a Ha Hs Hn). apply H1; auto. Qed.

(* [comment removed for export] *)
Fixpoint remove_first {A : Type} (eqb : A -> A -> bool) (x : A) (l : list A) : list A :=
  match l with [] => [] | y :: l' => if eqb x y then l' else y :: remove_first eqb x l' end.
Definition ck_eqb (u v : Z * Z) : bool := (fst u =? fst v) && (snd u =? snd v).

(* [comment removed for export] *)
Definition same_client (st st' : rtstate) : Prop :=
  st_sp0 st' = st_sp0 st /\ st_lb st' = st_lb st /\ st_lf st' = st_lf st /\ st_trs st' = st_trs st.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fp_class (st : rtstate) (c : Z) : list (Z * Z) :=
  [(rbeg st c, rbeg st c + KREGIONSIZE); (SH (rbeg st c), SH (rbeg st c) + KREGIONSIZE / 8); (rinfo st c, rinfo st c + 128)].
(* [comment removed for export] *)
Definition fp_tpage (st : rtstate) : list (Z * Z) := [(st_t st, st_t st + 4096)].
(* [comment removed for export] *)
Definition fp_emb (st' : rtstate) : list (Z * Z) :=
  (A_EMB, A_EMB + 56) :: (if emb_d st' =? 0 then [] else [(emb_d st', emb_d st' + EMB_CAP)]).
(* [comment removed for export] *)
Lemma errno_notin_fp_emb : forall st a, RTWF st -> AERRNO <= a < AERRNO + 4 -> ~ in_ivs (fp_emb st) a.
Proof.
  intros st a WF Ha (lo & hi & Hin & Hr). unfold fp_emb in Hin. destruct Hin as [E|Hin].
  - injection E as <- <-. unfold A_EMB, AERRNO, ATP in *. lia.
  - destruct (Z.eqb_spec (emb_d st) 0) as [E|NE]; [destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-.
    pose proof (emb_block_range st WF NE) as (R1 & _). unfold AERRNO, ATP, KHIGHMEM_BEG in *. blia.
Qed.
(* [comment removed for export] *)
Definition fp_wstatic : list (Z * Z) := ART_WSTATIC.
(* [comment removed for export] *)
Definition fp_depot_blocks (st : rtstate) : list (Z * Z) :=
  map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st)) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st)).

(* [comment removed for export] *)
Definition rt_post_std (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : word (* [comment removed for export] *) -> (word -> option byte) -> rtstate -> Model -> lghost -> Prop)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (st' : rtstate),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ P a0 m' st' mo' g'.


End CeilWrap.
End RTW_common_iface.

(* [comment removed for export] *)
Module RTW_depot_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art RTW_common_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition AUNWIND_IMPL : Z := 0x5c25c.   (* [comment removed for export] *)
Definition ADEPOT_PUT : Z := 0x743a4.     (* [comment removed for export] *)
Definition AUNWIND_STACK : Z := 256.     (* [comment removed for export] *)
Definition ADEPOT_STACK : Z := 1024.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition BST_SIZE : Z := 2064.
Definition trace_cells (tr : list Z) : list cell := map (fun pc => C8 (wz pc)) tr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unwind_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (S bp : Z) (tr : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 16 + 8 * zlen tr); (S + 2056, S + 2064);
              (st_t st + T_UNWINDING, st_t st + T_UNWINDING + 1)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ RTREP st m'                                                  (* [comment removed for export] *)
    /\ rw_cells bsegs m' (S + 8) [C4 (wz (zlen tr))]
    /\ rw_cells bsegs m' (S + 16) (trace_cells tr)
    /\ rw_cells bsegs m' (S + 2056) [C8 (wz bp)].

Definition unwind_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (S pc0 bp : Z) (rac s0c : word) (tl : list Z) (lo : Z),
  RTS st m mo g ->
  a0 = wz S -> a1 = wz pc0 -> a2 = wz bp -> a3 = wz 0 -> a4 = wz 1 -> a5 = wz TRACE_MAX_LEN ->
  tp = wz ATP ->
  (* [comment removed for export] *)
  rw_cells bsegs m S [C8 (wz (S + 16)); C4 (wz 0); C4 (wz 0)] -> wr_at bsegs m S BST_SIZE ->
  bv_unsigned sp <= S ->                                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  bv_unsigned sp <= bp - 16 -> bp < 2^64 -> 0 <= pc0 < 2^64 ->
  bytes_at bsegs m (bp - 16) (le8 s0c ++ le8 rac) -> 4096 <= bv_unsigned rac -> bv_unsigned rac <> pc0 ->
  (hop1_ok (st_sp0 st) bp = true -> uwt m bp (ASTACK_TOP (st_sp0 st)) pc0 bp (bv_unsigned s0c) 2 tl) ->
  (S + BST_SIZE <= bp - 16 \/ ASTACK_TOP (st_sp0 st) <= S) ->              (* [comment removed for export] *)
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AUNWIND_STACK ->
  mem_inv bsegs m ->
  evt bsegs (unwind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st S bp
               (hook_tr pc0 (st_sp0 st) bp (bv_unsigned rac) tl) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz AUNWIND_IMPL) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition same_but_depot (st st' : rtstate) : Prop :=
  st_sp0 st' = st_sp0 st /\ st_pbase st' = st_pbase st /\ st_spacebeg st' = st_spacebeg st
  /\ st_regions st' = st_regions st /\ st_cache_inited st' = st_cache_inited st /\ st_cache st' = st_cache st
  /\ st_pa st' = st_pa st /\ st_nreserved st' = st_nreserved st /\ st_sec st' = st_sec st
  /\ st_qthread st' = st_qthread st /\ st_qglobal st' = st_qglobal st
  /\ st_trs0 st' = st_trs0 st /\ st_fs st' = st_fs st /\ st_hints st' = st_hints st
  /\ st_lf st' = st_lf st /\ st_t st' = st_t st /\ st_ctx st' = st_ctx st /\ st_tls st' = st_tls st
  /\ st_loose0 st' = st_loose0 st /\ st_ia_inited st' = st_ia_inited st /\ st_lb st' = st_lb st
  /\ st_apend st' = st_apend st /\ st_spend st' = st_spend st /\ st_qpend st' = st_qpend st
  /\ st_qtmp st' = st_qtmp st /\ st_qcur st' = st_qcur st.

(* [comment removed for export] *)
Definition depot_fp (st' : rtstate) : list (Z * Z) :=
  (A_STACKSTORE, A_DEPOT_MAP1 + 8 * 2^15) :: fp_depot_blocks st'.

Definition depot_put_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (tr : list Z) (lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists id,
        a0' = wz id /\ 0 <= id < 2^32
        /\ same_but_depot st st' /\ trs_put tr (st_trs st) (st_trs st')
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ rt_frame (depot_fp st') lo (bv_unsigned sp) m m'
        /\ gmono g g' /\ budget_ok st g st' g' 0).

Definition depot_put_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (P : Z) (tr : list Z) (lo : Z),
  RTS st m mo g ->
  a0 = wz P -> a1 = wz (zlen tr) -> 1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr ->
  cells_at bsegs m P (trace_cells tr) -> (P + 8 * zlen tr <= lo \/ bv_unsigned sp <= P) ->
  alloc_ceiling <= P ->                                                    (* [comment removed for export] *)
  tp = wz ATP ->
  trs_room tr (st_trs st) ->
  rt_prov st <= g_res g ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ADEPOT_STACK ->
  mem_inv bsegs m ->
  LSCPS bsegs (depot_put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st tr lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ADEPOT_PUT) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)


End CeilWrap.
End RTW_depot_iface.

(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
Module RTW_m_lib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art RTW_common_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma sx32_lit : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap.
  change (bv_swrap 32 (e mod 2^64)) with (((e mod 2^64) + 2^31) mod 2^32 - 2^31).
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma zx32_lit : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite (unsigned_lit z) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma shl32_shr30 : forall x, 0 <= x < 2^30 -> Z.shiftr ((Z.shiftl x 32) mod 2^64) 30 = 4 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by lia.
  change (2^32) with (4 * 2^30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma shl32_shr32 : forall x, 0 <= x < 2^32 -> Z.shiftr ((Z.shiftl x 32) mod 2^64) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by lia. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fp_covers (FP : list (Z * Z)) (lo SP : Z) (W : list (Z * Z)) : Prop :=
  forall iv, In iv W -> (lo <= fst iv /\ snd iv <= SP) \/ exists f, In f FP /\ fst f <= fst iv /\ snd iv <= snd f.

Lemma outside_of_cover : forall FP lo SP W a,
  fp_covers FP lo SP W -> ~ (lo <= a < SP) -> ~ in_ivs FP a -> outside W a.
Proof.
  intros FP lo SP W a HC HS HN. induction W as [|[l h] W IH]; [exact I|]. cbn. split.
  - destruct (HC (l, h) ltac:(left; reflexivity)) as [[H1 H2]|(f & Hf & H1 & H2)]; cbn [fst snd] in *; [lia|].
    intros Hin. apply HN. exists (fst f), (snd f). split; [destruct f; exact Hf| lia].
  - apply IH. intros iv Hiv. apply HC. right. exact Hiv.
Qed.

Lemma rt_frame_of_munch : forall FP lo SP W m m',
  munch W m m' -> fp_covers FP lo SP W -> rt_frame FP lo SP m m'.
Proof.
  intros FP lo SP W m m' MU HC a Ha HS HN. apply MU. rewrite wa_unsigned by lia. eapply outside_of_cover; eauto.
Qed.

(* [comment removed for export] *)
Lemma cj_pres_of_munch : forall sp0 LB LF SP W m m',
  munch W m m' -> wmono bsegs m m' ->
  (forall a, 0 <= a < 2^64 -> cj_client_addr sp0 LB LF SP a -> outside W a) ->
  cj_pres sp0 LB LF SP m m'.
Proof.
  intros sp0 LB LF SP W m m' MU WM HO a Ha HC. split.
  - apply MU. rewrite wa_unsigned by lia. apply HO; assumption.
  - apply WM.
Qed.

Lemma outside_app : forall W1 W2 a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[l h] W1 IH]; intros; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma outside_cons : forall l h W a, outside ((l, h) :: W) a <-> (~ (l <= a < h)) /\ outside W a.
Proof. intros. cbn. tauto. Qed.


End CeilWrap.
End RTW_m_lib.

(* [comment removed for export] *)
Module RTW_malloc_leaves_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art RTW_common_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Definition A_GET_CURRENT_THREAD : Z := 0x5dcc4.   (* [comment removed for export] *)
Definition A_GET_THREAD_STATS : Z := 0x5ce90.     (* [comment removed for export] *)
Definition A_RZSIZE2LOG : Z := 0x37488.           (* [comment removed for export] *)
Definition A_RUN_MALLOC_HOOKS : Z := 0x62498.     (* [comment removed for export] *)
Definition A_RUN_FREE_HOOKS : Z := 0x62554.       (* [comment removed for export] *)
Definition A_SET_ERRNO_ENOMEM : Z := 0x6e13c.     (* [comment removed for export] *)
Definition A_INTERNAL_ALLOCATOR : Z := 0x5fd40.   (* [comment removed for export] *)
Definition A_INTERNAL_MEMSET : Z := 0x65840.      (* [comment removed for export] *)
Definition A_TRY_ASAN_INIT : Z := 0x5b4c4.        (* [comment removed for export] *)
Definition A_ASAN_INITED_FN : Z := 0x5a5b4.       (* [comment removed for export] *)
Definition A_GET_MALLOC_CTX_SIZE : Z := 0x5c24c.  (* [comment removed for export] *)
Definition A_GET_CURRENT_PC : Z := 0x74d28.       (* [comment removed for export] *)
Definition A_CAN_POISON_FN : Z := 0x55694.        (* [comment removed for export] *)
Definition A_MAY_RETURN_NULL_FN : Z := 0x60254.   (* [comment removed for export] *)
Definition A_RSS_EXCEEDED_FN : Z := 0x6027c.      (* [comment removed for export] *)
Definition A_SET_OOM_FN : Z := 0x60244.           (* [comment removed for export] *)
Definition A_LSAN_DISABLED_FN : Z := 0x818a4.    (* [comment removed for export] *)
Definition ENOMEM : Z := 12.

(* [comment removed for export] *)
Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (lo : Z) (m : word -> option byte)
    (P : word (* [comment removed for export] *) -> word (* [comment removed for export] *) -> (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp) /\ P a0 a1 m'.

Section Leaves.
(* [comment removed for export] *)
Local Notation "'REGS'" := (forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word), True) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition get_current_thread_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> RTWF st -> mem_inv bsegs m -> tp = wz ATP ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
               (fun a0' _ _ => a0' = wz (st_t st)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_GET_CURRENT_THREAD) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition get_thread_stats_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> RTWF st -> mem_inv bsegs m -> tp = wz ATP ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
               (fun a0' _ _ => a0' = wz (st_t st + T_STATS)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_GET_THREAD_STATS) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition rzsize2log_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k lo : Z),
  mem_inv bsegs m -> 0 <= k <= 7 -> a0 = wz (Z.shiftl 16 k) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
               (fun a0' _ _ => a0' = wz k))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_RZSIZE2LOG) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition run_malloc_hooks_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
               (fun _ _ _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_RUN_MALLOC_HOOKS) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition run_free_hooks_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
               (fun a0' _ _ => a0' = wz 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_RUN_FREE_HOOKS) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition set_errno_enomem_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (errv : word) (lo : Z),
  mem_inv bsegs m -> tp = wz ATP -> rw_cells bsegs m AERRNO [C4 errv] ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (AERRNO, AERRNO + 4)] lo m
               (fun _ _ m' => rw_cells bsegs m' AERRNO [C4 (wz ENOMEM)]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_SET_ERRNO_ENOMEM) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition internal_memset_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s c n : Z) (junk : list byte) (lo : Z),
  mem_inv bsegs m -> a0 = wz s -> a1 = wz c -> a2 = wz n -> 0 <= c < 256 -> 0 <= n -> s + n < 2^64 ->
  rw_cells bsegs m s [CB (Z.to_nat n) junk] -> (s + n <= lo \/ bv_unsigned sp <= s) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(s, s + n)] lo m
               (fun _ _ m' => rw_cells bsegs m' s [CB (Z.to_nat n) (repeat (zb c) (Z.to_nat n))]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_INTERNAL_MEMSET) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition set_ia_inited (st : rtstate) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 _ a23 b1 b2 b3 b4 b5 =>
    mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 true a23 b1 b2 b3 b4 b5
  end.
Definition A_IA_SIZE : Z := 0x81030.

Definition internal_allocator_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> RTWF st -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 48, bv_unsigned sp); (A_IA_INSTANCE, A_IA_INSTANCE + A_IA_SIZE); (A_IA_INITED, A_IA_INITED + 4)] lo m
               (fun a0' _ m' => a0' = wz A_IA_INSTANCE /\ RTREP (set_ia_inited st) m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_INTERNAL_ALLOCATOR) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition tiny_spec (entry : Z) (needs_tp : bool) (res : word -> word -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> mem_inv bsegs m -> (needs_tp = true -> tp = wz ATP) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
               (fun a0' _ _ => res ra a0'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz entry) fc None m (seg_rom bsegs)).

Definition try_asan_init_spec : Prop := tiny_spec A_TRY_ASAN_INIT false (fun _ a0' => a0' = wz 1).        (* [comment removed for export] *)
Definition asan_inited_spec : Prop := tiny_spec A_ASAN_INITED_FN false (fun _ a0' => a0' = wz 1).         (* [comment removed for export] *)
Definition get_malloc_ctx_size_spec : Prop := tiny_spec A_GET_MALLOC_CTX_SIZE false (fun _ a0' => a0' = wz TRACE_MAX_LEN).  (* [comment removed for export] *)
Definition get_current_pc_spec : Prop := tiny_spec A_GET_CURRENT_PC false (fun ra a0' => a0' = ra).
Definition can_poison_spec : Prop := tiny_spec A_CAN_POISON_FN false (fun _ a0' => a0' = wz 1).           (* [comment removed for export] *)
Definition may_return_null_spec : Prop := tiny_spec A_MAY_RETURN_NULL_FN false (fun _ a0' => a0' = wz 1). (* [comment removed for export] *)
Definition rss_exceeded_spec : Prop := tiny_spec A_RSS_EXCEEDED_FN false (fun _ a0' => a0' = wz 0).       (* [comment removed for export] *)
Definition lsan_disabled_spec : Prop := tiny_spec A_LSAN_DISABLED_FN true (fun _ a0' => a0' = wz 0).       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition set_oom_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> RTWF st -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(A_ALLOC_OOM, A_ALLOC_OOM + 1)] lo m
               (fun _ _ m' => RTREP st m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_SET_OOM_FN) fc None m (seg_rom bsegs)).
End Leaves.

(* [comment removed for export] *)


End CeilWrap.
End RTW_malloc_leaves_iface.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art.
Import RTW_common_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition AREFILL : Z := 0x36d10.          (* [comment removed for export] *)
Definition ACDEALLOC : Z := 0x3457c.        (* [comment removed for export] *)
Definition AREFILL_STACK : Z := 2560.       (* [comment removed for export] *)
Definition ACDEALLOC_STACK : Z := 2048.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition same_but_primary (st st' : rtstate) : Prop :=
  st_sp0 st' = st_sp0 st /\ st_pbase st' = st_pbase st /\ st_spacebeg st' = st_spacebeg st
  /\ st_pa st' = st_pa st /\ st_nreserved st' = st_nreserved st /\ st_sec st' = st_sec st
  /\ st_qthread st' = st_qthread st /\ st_qglobal st' = st_qglobal st /\ st_depot st' = st_depot st
  /\ st_trs st' = st_trs st /\ st_trs0 st' = st_trs0 st /\ st_fs st' = st_fs st /\ st_hints st' = st_hints st
  /\ st_lf st' = st_lf st /\ st_t st' = st_t st /\ st_ctx st' = st_ctx st /\ dtls_same st st'
  /\ loose0_ext st st' /\ st_ia_inited st' = st_ia_inited st /\ st_lb st' = st_lb st
  /\ st_spend st' = st_spend st /\ st_qpend st' = st_qpend st /\ st_qtmp st' = st_qtmp st /\ st_qcur st' = st_qcur st.

(* [comment removed for export] *)
Definition primary_fp (st : rtstate) (c : Z) : list (Z * Z) := fp_class st c ++ fp_tpage st.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition refill_rel (st st' : rtstate) (cls : Z) (r : Z) : Prop :=
  same_but_primary st st' /\ st_apend st' = st_apend st /\ st_cache_inited st' = true
  /\ (forall c, 0 <= c < KNUMCLASSES -> c <> cls -> rg st' c = rg st c /\ cch st' c = cch st c)
  /\ ((r = 1 /\ zlen (cch st' cls) = nrefill cls) \/ (r = 0 /\ cch st' cls = [])).

Definition refill_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (cls lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists r,
        a0' = wz r /\ refill_rel st st' cls r
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ rt_frame (primary_fp st cls ++ fp_emb st') lo (bv_unsigned sp) m m'   (* [comment removed for export] *)
        /\ gmono g g' /\ budget_ok st g st' g' 0).

Definition refill_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (cls lo : Z),
  RTS st m mo g ->
  1 <= cls <= 30 -> cch st cls = [] ->
  a0 = wz (acache st) -> a1 = wz (pcaddr st cls) -> a2 = wz A_ALLOC -> a3 = wz cls ->
  tp = wz ATP ->
  rt_prov st <= g_res g ->                       (* [comment removed for export] *)
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  mem_inv bsegs m ->
  LSCPS bsegs (refill_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AREFILL) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)
Definition refill2_post (r : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (cls lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' =>
        a0' = wz r /\ refill_rel st st' cls r
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ rt_frame (primary_fp st cls ++ fp_emb st') lo (bv_unsigned sp) m m'   (* [comment removed for export] *)
        /\ gmono g g' /\ budget_ok st g st' g' 0).

Definition refill_spec2_fresh : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (cls lo : Z),
  RTS st m mo g ->
  1 <= cls <= 30 -> fresh_cls st cls ->
  a0 = wz (acache st) -> a1 = wz (pcaddr st cls) -> a2 = wz A_ALLOC -> a3 = wz cls ->
  tp = wz ATP ->
  rt_prov st <= g_res g ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  mem_inv bsegs m ->
  LSCPS2 bsegs (refill2_post 0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m g)
               (refill2_post 1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AREFILL) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cdealloc_rel (st st' : rtstate) (c k : Z) : Prop :=
  same_but_primary st st' /\ st_apend st' = remove_first ck_eqb (c, k) (st_apend st) /\ st_cache_inited st' = true
  /\ (forall c', 0 <= c' < KNUMCLASSES -> c' <> c -> rg st' c' = rg st c' /\ cch st' c' = cch st c')
  /\ In k (avail_cptrs st' c).

Definition cdealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (c k lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun _ m' st' mo' g' =>
        cdealloc_rel st st' c k
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ rt_frame (primary_fp st c) lo (bv_unsigned sp) m m'
        /\ gmono g g' /\ budget_ok st g st' g' 0).

Definition cache_dealloc_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (c k lo : Z),
  RTS st m mo g ->
  In (c, k) (st_apend st) ->
  a0 = wz (acache st) -> a1 = wz A_ALLOC -> a2 = wz c -> a3 = wz (cptr_addr st c k) ->
  tp = wz ATP ->
  rt_prov st <= g_res g ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ACDEALLOC_STACK ->
  mem_inv bsegs m ->
  LSCPS bsegs (cdealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st c k lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ACDEALLOC) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)


End CeilWrap.
