(** U/Prog/HeadCheck/KeyCut.v's [val_stmt] from Cut.v's [near_stmt]: the walk 0x14554 -> 0x144f4 / 0x146fc of the
    UBSan LLVMFuzzerTestOneInput (fuzz_headamp.c:94-107 and :140-141). The &ent[v] checks (traps 0x14558 / 0x1455c
    not taken: v < 32 and pp + OFF_ENT + 104 v is below the stack), the type dispatch, pod_bool / pod_int / pod_float
    (with the nearest piece applied at 0x145ec), and value <= top at 0x146f4 / 0x146f8. Each branch the code takes
    decides one case of Pod/Headamp.v [cell_value] (Prog/HeadCheck/KeyFacts.v cv_bool, cv_int, cv_float, cv_small,
    cv_other). The bool and int paths write no memory and keep the FP state; the float path's changes are the nearest
    piece's own. Walked backwards: the exits ([ref_ok] 0x144f4, [cell_ok] 0x146fc), [ref0_ok] (0x145e0, the reloads of
    a refusal), [top_ok] (0x146f4), [bool_ok] (0x14584), [int_ok] (0x145a8), [float_ok] (0x145d0), [val_ok]
    (0x14554). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts KeyFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut KeyCut.
Import ListNotations.
Open Scope Z_scope.

(* Register equations at a lemma's entry. *)
Ltac weq := first [ reflexivity
                  | (f_equal; lia)
                  | (f_equal; unfold OFF_ENT, ENT_SIZE; lia) ].

Section Val.
Variables (Q : machine_state -> Prop) (sp gp tp s1 s2 s3 s4 s5 s6 s9 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo pp p : Z) (v : nat) (e : ent) (w68 w98 wa8 wb0 : word).

Local Abbreviation SP := (bv_unsigned sp).
Local Abbreviation EA := (pp + OFF_ENT + ENT_SIZE * Z.of_nat v).
Local Abbreviation S0 := (Z_to_bv 64 (2^64 - 1 - (pp + OFF_ENT))).
Local Abbreviation S8 := (Z_to_bv 64 (pp + OFF_ENT)).
Local Abbreviation A7 := (Z_to_bv 64 (pp + OFF_ENT + 8)).

Hypothesis HV : (v < 32)%nat.
Hypothesis HEB : bytes_at rsegs m EA (ent_mem e).
Hypothesis HEW : ent_wf e.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + POD_PROPS <= lo.
Hypothesis H68 : bytes_at rsegs m (SP + 0x68) (le8 w68).
Hypothesis H98 : bytes_at rsegs m (SP + 0x98) (le8 w98).
Hypothesis HA0 : bytes_at rsegs m (SP + 0xa0) (le8 A7).
Hypothesis HA8 : bytes_at rsegs m (SP + 0xa8) (le8 wa8).
Hypothesis HB0 : bytes_at rsegs m (SP + 0xb0) (le8 wb0).
Hypothesis HF9 : Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1).
Hypothesis HF18 : Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256).
Hypothesis HF19 : Sem.reg_get F (Z_to_bv 5 19) = Sem.nan_box (Z_to_bv 32 F32_2P63).
Hypothesis H48 : bytes_at rsegs m (SP + 0x48) (le8 (Z_to_bv 64 MHALF_HI)).
Hypothesis H50 : bytes_at rsegs m (SP + 0x50) (le8 (Z_to_bv 64 HALF_HI)).
Hypothesis H58 : bytes_at rsegs m (SP + 0x58) (le8 (Z_to_bv 64 C2_HI)).
Hypothesis H60 : bytes_at rsegs m (SP + 0x60) (le8 (Z_to_bv 64 C2_LO)).
Hypothesis HST : stk rsegs m lo (SP + FRAME_LOCALS).
Hypothesis HLO : lo + NEAR_STACK <= SP.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Hypothesis HFC : frm0 fc.
Hypothesis HMI : mem_inv rsegs m.
Hypothesis HTM : MemNorm.task_mem rsegs m.

Hypothesis HREF : forall (t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte),
       (cell_value e <? 0) || (ktop p <? cell_value e) = true ->
       frm0 fc' ->
       (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) ->
       munch (NEAR_W SP) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (SP + FRAME_LOCALS) ->
       evt rsegs Q
         (MS (mkR wa8 sp gp tp t0' t1' t2' S0 s1 a0' a1' w68 a3' a4' (Z_to_bv 64 REFUSE_OUT_OF_RANGE) w98 A7
                  s2 s3 s4 s5 s6 s7' S8 s9 s10' (Z_to_bv 64 (ktop p)) t3' t4' (Z_to_bv 64 8) wb0)
             F' (Z_to_bv 64 0x144f4) fc' None m' (seg_rom rsegs)).

Hypothesis HCELL : forall (t0' t1' t2' a0' a1' a5' s10' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte),
       (cell_value e <? 0) || (ktop p <? cell_value e) = false ->
       frm0 fc' ->
       (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) ->
       munch (NEAR_W SP) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (SP + FRAME_LOCALS) ->
       evt rsegs Q
         (MS (mkR wa8 sp gp tp t0' t1' t2' S0 s1 a0' a1' w68 (Z_to_bv 64 9) (Z_to_bv 64 p) a5' w98 A7
                  s2 s3 s4 s5 s6 (Z_to_bv 64 (cell_value e)) S8 s9 s10' (Z_to_bv 64 (ktop p))
                  t3' t4' (Z_to_bv 64 8) wb0)
             F' (Z_to_bv 64 0x146fc) fc' None m' (seg_rom rsegs)).

Hypothesis NEAR : near_stmt.

(** The numbers lia needs. *)
Lemma bnd : 0 <= pp /\ pp + 19744 <= lo /\ lo + 48 <= SP /\ SP + 0x1d8 <= 2^64 /\ (v < 32)%nat.
Proof.
  pose proof HST as (H0 & H1 & _). pose proof HPPLO as H2. pose proof HLO as H3.
  unfold POD_PROPS, NEAR_STACK, FRAME_LOCALS in *. lia.
Qed.

(** What the exits keep: the FP registers off f8 / f10, frm 0, the memory changed only in NEAR_W. *)
Definition Post (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) : Prop :=
  frm0 fc' /\ (forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r) /\
  munch (NEAR_W SP) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\
  stk rsegs m' lo (SP + FRAME_LOCALS).

Lemma Post_refl : Post F fc m.
Proof.
  exact (conj HFC (conj (fun r _ _ => eq_refl) (conj (munch_refl _ m) (conj (wmono_refl rsegs m)
           (conj HMI (conj HTM HST)))))).
Qed.

(** ** The exits *)
(** 0x144f4: the refusal fold, with OUT_OF_RANGE. *)
Lemma ref_ok : forall (t0 t1 t2 a0 a1 a3 a4 s7 s10 t3 t4 : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m' : word -> option byte),
  (cell_value e <? 0) || (ktop p <? cell_value e) = true -> Post F' fc' m' ->
  evt rsegs Q (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 w68 a3 a4 (Z_to_bv 64 5) w98 A7 s2 s3 s4 s5 s6 s7 S8 s9 s10
                       (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0) F' (Z_to_bv 64 0x144f4) fc' None m' (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a3 a4 s7 s10 t3 t4 F' fc' m' HC (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  exact (HREF t0 t1 t2 a0 a1 a3 a4 s7 s10 t3 t4 F' fc' m' HC P1 P2 P3 P4 P5 P6 P7).
Qed.

(** 0x146fc: the cap test, with s7 = the value. *)
Lemma cell_ok : forall (t0 t1 t2 a0 a1 a5 s10 t3 t4 : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m' : word -> option byte),
  (cell_value e <? 0) || (ktop p <? cell_value e) = false -> Post F' fc' m' ->
  evt rsegs Q (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 w68 (Z_to_bv 64 9) (Z_to_bv 64 p) a5 w98 A7 s2 s3 s4 s5 s6
                       (Z_to_bv 64 (cell_value e)) S8 s9 s10 (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0)
                   F' (Z_to_bv 64 0x146fc) fc' None m' (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a5 s10 t3 t4 F' fc' m' HC (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  exact (HCELL t0 t1 t2 a0 a1 a5 s10 t3 t4 F' fc' m' HC P1 P2 P3 P4 P5 P6 P7).
Qed.

(** 0x145e0 .. 0x145e8: a refusal of cell_value (-1): a2 / a6 reloaded, then the fold. *)
Lemma ref0_ok : forall (t0 t1 t2 a0 a1 a2 a3 a4 a6 s7 s10 t3 t4 : word),
  cell_value e = -1 ->
  evt rsegs Q (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 5) a6 A7 s2 s3 s4 s5 s6 s7 S8 s9 s10
                       (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0) F (Z_to_bv 64 0x145e0) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a6 s7 s10 t3 t4 CV.
  (* 0x145e0 ld a2,0x68(sp); ld a6,0x98(sp); j 0x144f4 *)
  pose proof (read_le8 rsegs m _ _ H68) as HR. step. clear HR.
  pose proof (read_le8 rsegs m _ _ H98) as HR. step. clear HR.
  step.
  apply ref_ok; [rewrite CV; reflexivity | exact Post_refl].
Qed.

(** 0x146f4 .. 0x146f8: value <= top (fuzz_headamp.c:141) on s7 = the value in [0, 255]. *)
Lemma top_ok : forall (t0 t1 t2 a0 a1 s10 t3 t4 : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m' : word -> option byte) (val : Z),
  cell_value e = val -> 0 <= val <= 255 -> Post F' fc' m' ->
  evt rsegs Q (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 w68 (Z_to_bv 64 9) (Z_to_bv 64 p) (Z_to_bv 64 5) w98 A7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 val) S8 s9 s10 (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0)
                   F' (Z_to_bv 64 0x146f4) fc' None m' (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 s10 t3 t4 F' fc' m' val CV Hv HP. subst val.
  pose proof (ktop_range p) as Ht.
  (* 0x146f4 sext.w a0,s7 *)
  step. rewrite sextw_small by lia.
  (* 0x146f8 bltu s11,a0 *)
  step. rewrite ltu_u by lia.
  (* a case split that leaves HREF / HCELL (which mention ktop p <? cell_value e) unchanged *)
  destruct (Z.lt_ge_cases (ktop p) (cell_value e)) as [L|L].
  - rewrite (proj2 (Z.ltb_lt _ _) L). cbv beta iota.
    apply ref_ok; [|exact HP]. apply orb_true_iff. right. apply Z.ltb_lt. exact L.
  - rewrite (proj2 (Z.ltb_ge _ _) L). cbv beta iota.
    apply cell_ok; [|exact HP]. apply orb_false_iff. split; apply Z.ltb_ge; lia.
Qed.

(** ** cell_value (fuzz_headamp.c:94-107) on ent[v] at a0 = EA *)
(** 0x14584 .. 0x145a4: pod_bool (type 2 passed): size < 4 refuses, else s7 = (word != 0), then the cap test. *)
Lemma bool_ok : forall (t0 t1 t2 a0 a1 a2 a6 t3 t4 : word),
  e_type e = POD_BOOL -> a0 = Z_to_bv 64 EA ->
  evt rsegs Q (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 (Z_to_bv 64 9) (Z_to_bv 64 p) (Z_to_bv 64 5) a6 A7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (ENT_SIZE * Z.of_nat v)) S8 s9 (Z_to_bv 64 (Z.of_nat v))
                       (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0) F (Z_to_bv 64 0x14584) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a6 t3 t4 Ht ->.
  pose proof bnd as (B0 & B1 & B2 & B3 & B4). pose proof HEW as (Ht0 & Hb & Hsz). pose proof (ktop_range p) as Htop.
  (* 0x14584 lw a0,4(a0); ld a2,0x68(sp); addi a1,zero,4; ld a6,0x98(sp); bltu a0,a1 *)
  pose proof (ent_size_read rsegs m _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  pose proof (read_le8 rsegs m _ _ H68) as HR. step. clear HR. step.
  pose proof (read_le8 rsegs m _ _ H98) as HR. step. clear HR.
  step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size e) 4) as [Es|Es]; cbv beta iota.
  { apply ref_ok; [rewrite (cv_small e Es); reflexivity | exact Post_refl]. }
  (* 0x14598 add s7,a7,s7; lw a0,0(s7); snez s7,a0; j 0x146fc *)
  step.
  pose proof (ent_word_read rsegs m _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite sext_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn.
  step. rewrite snez_s32 by (apply rd32_range).
  step.
  pose proof (cv_bool e Ht ltac:(lia)) as CV. rewrite <- CV.
  apply cell_ok; [|exact Post_refl].
  rewrite CV. destruct (negb (rd32 (e_body e) =? 0)); apply orb_false_iff; split; apply Z.ltb_ge; lia.
Qed.

(** 0x145a8 .. 0x145cc: pod_int: size < 4 refuses, s7 = the int32, 0 <= s7 < 256 (unsigned test) or a refusal. *)
Lemma int_ok : forall (t0 t1 t2 a0 a1 a2 a6 t3 t4 : word),
  e_type e = POD_INT -> a0 = Z_to_bv 64 EA ->
  evt rsegs Q (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 (Z_to_bv 64 9) (Z_to_bv 64 p) (Z_to_bv 64 5) a6 A7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (ENT_SIZE * Z.of_nat v)) S8 s9 (Z_to_bv 64 (Z.of_nat v))
                       (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0) F (Z_to_bv 64 0x145a8) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a6 t3 t4 Ht ->.
  pose proof bnd as (B0 & B1 & B2 & B3 & B4). pose proof HEW as (Ht0 & Hb & Hsz).
  (* 0x145a8 lw a0,4(a0); addi a1,zero,4; bltu a0,a1 *)
  pose proof (ent_size_read rsegs m _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size e) 4) as [Es|Es]; cbv beta iota.
  { apply ref0_ok. apply cv_small. exact Es. }
  (* 0x145b4 add s7,a7,s7; lw s7,0(s7) *)
  step.
  pose proof (ent_word_read rsegs m _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite sext_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn.
  (* 0x145bc ld a2,0x68(sp); addi a0,zero,0x100; ld a6,0x98(sp); bgeu s7,a0 *)
  pose proof (read_le8 rsegs m _ _ H68) as HR. step. clear HR. step.
  pose proof (read_le8 rsegs m _ _ H98) as HR. step. clear HR.
  pose proof (s32_range _ (rd32_range (e_body e))) as Hi.
  step. rewrite int_ltu256 by lia.
  pose proof (cv_int e Ht ltac:(lia)) as CV. revert CV.
  destruct ((0 <=? s32 (rd32 (e_body e))) && (s32 (rd32 (e_body e)) <=? 255)) eqn:Ei; cbn [negb]; cbv beta iota;
    intros CV.
  - (* 0x145cc j 0x146f4 *)
    step. apply andb_prop in Ei as [Ei1 Ei2]. apply Z.leb_le in Ei1. apply Z.leb_le in Ei2.
    eapply top_ok; [exact CV | lia | exact Post_refl].
  - apply ref_ok; [rewrite CV; reflexivity | exact Post_refl].
Qed.

(** 0x145d0 .. 0x145dc: pod_float: size < 4 refuses, else the nearest piece from 0x145ec: Some n goes on to
    value <= top, None refuses. *)
Lemma float_ok : forall (t0 t1 t2 a0 a1 a2 a6 a7 t3 t4 : word),
  e_type e = POD_FLOAT -> a0 = Z_to_bv 64 EA ->
  evt rsegs Q (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 (Z_to_bv 64 9) (Z_to_bv 64 p) (Z_to_bv 64 5) a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (ENT_SIZE * Z.of_nat v)) S8 s9 (Z_to_bv 64 (Z.of_nat v))
                       (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0) F (Z_to_bv 64 0x145d0) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a6 a7 t3 t4 Ht ->.
  pose proof bnd as (B0 & B1 & B2 & B3 & B4). pose proof HEW as (Ht0 & Hb & Hsz).
  (* 0x145d0 lw a0,4(a0); addi a1,zero,4; ld a7,0xa0(sp); bgeu a0,a1 *)
  pose proof (ent_size_read rsegs m _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step.
  pose proof (read_le8 rsegs m _ _ HA0) as HR. step. clear HR.
  step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size e) 4) as [Es|Es]; cbn [negb]; cbv beta iota.
  { apply ref0_ok. apply cv_small. exact Es. }
  (* 0x145ec: the inlined pod_nearest(f, 0, 255) *)
  assert (HBL : (4 <= length (e_body e))%nat) by lia.
  apply NEAR with (lo := lo) (pp := pp) (v := v) (e := e) (w68 := w68) (w98 := w98) (wa0 := A7) (wa8 := wa8)
    (wb0 := wb0).
  all: try (first [reflexivity | assumption]).
  intros t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' F' fc' m' HF' HFk MU WM MI TM ST.
  assert (HP : Post F' fc' m') by exact (conj HF' (conj HFk (conj MU (conj WM (conj MI (conj TM ST)))))).
  pose proof (cv_float e Ht ltac:(lia)) as CV. revert CV.
  destruct (nearest (rd32 (e_body e)) 0 255) as [n|] eqn:EN; intros CV.
  - pose proof (nearest_range _ _ _ _ EN) as Hn.
    eapply top_ok; [exact CV | lia | exact HP].
  - apply ref_ok; [rewrite CV; reflexivity | exact HP].
Qed.

(** 0x14554 .. 0x14580: the &ent[v] checks (v < 33; ent + 104 v does not wrap) and the type dispatch. *)
Lemma val_ok : forall (t0 t1 t2 a0 a1 a2 a6 a7 t3 t4 : word),
  evt rsegs Q (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 (Z_to_bv 64 9) (Z_to_bv 64 p) (Z_to_bv 64 5) a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (ENT_SIZE * Z.of_nat v)) S8 s9 (Z_to_bv 64 (Z.of_nat v))
                       (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0) F (Z_to_bv 64 0x14554) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a6 a7 t3 t4.
  pose proof bnd as (B0 & B1 & B2 & B3 & B4). pose proof HEW as (Ht0 & Hb & Hsz).
  (* 0x14554 addi a0,zero,0x21; bgeu s10,a0 *)
  step. step. rewrite ltu_u by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb]. cbv beta iota.
  (* 0x1455c bltu s0,s7 *)
  step. rewrite ltu_u by (unfold OFF_ENT, ENT_SIZE; lia).
  rewrite (proj2 (Z.ltb_ge _ _)) by (unfold OFF_ENT, ENT_SIZE; lia). cbv beta iota.
  (* 0x14560 add a0,s8,s7; lw a1,0(a0) *)
  step.
  pose proof (ent_type_read rsegs m _ _ HEB Ht0) as HR. step. clear HR.
  (* 0x14568 addi a2,zero,6; beq a1,a2 *)
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type e) 6) as [E6|E6]; cbv beta iota.
  { eapply float_ok; [exact E6 | weq]. }
  (* 0x14570 addi a2,zero,4; ld a7,0xa0(sp); beq a1,a2 *)
  step.
  pose proof (read_le8 rsegs m _ _ HA0) as HR. step. clear HR.
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type e) 4) as [E4|E4]; cbv beta iota.
  { eapply int_ok; [exact E4 | weq]. }
  (* 0x1457c addi a2,zero,2; bne a1,a2 *)
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type e) 2) as [E2|E2]; cbn [negb]; cbv beta iota.
  2:{ apply ref0_ok. apply cv_other; unfold POD_BOOL, POD_INT, POD_FLOAT; lia. }
  eapply bool_ok; [exact E2 | weq].
Qed.

End Val.

Theorem val_holds : near_stmt -> val_stmt.
Proof.
  intros NEAR Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo pp p v e w68 w98 wa8 wb0 -> -> -> -> -> -> -> -> -> -> -> HV HEB HEW HPP0 HPPLO H68 H98 HA0 HA8 HB0
    HF9 HF18 HF19 H48 H50 H58 H60 HST HLO HSPA HROM HFC HMI HTM HREF HCELL.
  eapply val_ok with (Q := Q) (F := F) (fc := fc) (m := m) (lo := lo) (pp := pp) (p := p) (v := v) (e := e)
    (w68 := w68) (w98 := w98) (wa8 := wa8) (wb0 := wb0); eassumption.
Qed.
