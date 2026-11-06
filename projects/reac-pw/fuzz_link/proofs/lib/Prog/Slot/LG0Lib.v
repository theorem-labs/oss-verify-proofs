(* ARM 0 (op_read) at the SR level, part 1: the facts the glue of LG0.v uses.
   - CUT bookkeeping: an existential of the cut predicate leaves the CUT (g0_cut_ex), an eqv_cl closure of
     it is dropped (g0_cut_cl), a pure fact is read off it (g0_cut_pure);
   - the canonical register map of a return address: an mkR map rebuilt from the caller's callee-saved
     words and the callee's other registers (g0_canon, g0_ms_eqv);
   - the payload block is an entry block (g0_pl_blocks, g0_pl_in), so LFrLo.lh_reg lies in LFr.lkeep;
   - the arm's memory facts (LC0Defs c0_frame, c0_base, a text_buf buffer) survive an allocator call;
   - a fresh block of text_buf is an LC0Defs c0_blk;
   - the slot's blocks hb along the arm: lroom_hb, opt_hb, and the hp side condition of cut_evt. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrLo LFrEn LGlue
  LC0Defs LC45Call.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Destructing the existentials of a cut predicate
   ========================================================================== *)

Ltac g0_ex H := repeat match type of H with exists _, _ => let x := fresh "x" in destruct H as [x H] end.

(* ==========================================================================
   2. The canonical register map at a return address
   ========================================================================== *)

Section Canon.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.

Lemma g0_canon : forall regs' a0',
  regs_preserved (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 regs' ->
  reg_get regs' (Z_to_bv 5 10) = a0' ->
  Regs6ss.xregs_eqv
    (mkR (reg_get regs' (Z_to_bv 5 1)) sp gp tp (reg_get regs' (Z_to_bv 5 5)) (reg_get regs' (Z_to_bv 5 6))
         (reg_get regs' (Z_to_bv 5 7)) s0 s1 a0' (reg_get regs' (Z_to_bv 5 11)) (reg_get regs' (Z_to_bv 5 12))
         (reg_get regs' (Z_to_bv 5 13)) (reg_get regs' (Z_to_bv 5 14)) (reg_get regs' (Z_to_bv 5 15))
         (reg_get regs' (Z_to_bv 5 16)) (reg_get regs' (Z_to_bv 5 17)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         (reg_get regs' (Z_to_bv 5 28)) (reg_get regs' (Z_to_bv 5 29)) (reg_get regs' (Z_to_bv 5 30))
         (reg_get regs' (Z_to_bv 5 31)))
    regs'.
Proof.
  intros regs' a0' RP H10.
  assert (C : forall r, callee_saved r -> reg_get regs' (Z_to_bv 5 r) =
      reg_get (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              (Z_to_bv 5 r)).
  { intros r Hr. pose proof (RP r Hr) as H. unfold YK11.getr in H. unfold callee_saved in Hr.
    replace (bv_eqb (Z_to_bv 5 r) 0) with false in H; [exact H|].
    symmetry. unfold bv_eqb. rewrite Z_to_bv_unsigned. apply Z.eqb_neq. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia.
    intros E. assert (Z0 : bv_unsigned (0 : bv 5) = 0) by (vm_compute; reflexivity). rewrite Z0 in E. lia. }
  apply Regs6ss.xregs_eqv_sym. apply Regs6ss.mkR_eqv_of;
    first [ reflexivity
          | exact H10
          | match goal with |- reg_get regs' ?l = _ =>
              let z := eval vm_compute in (bv_unsigned l) in exact (C z ltac:(unfold callee_saved; lia)) end ].
Qed.
End Canon.

Lemma g0_ms_eqv : forall X R F pc fc m ro, Regs6ss.xregs_eqv X R ->
  Regs6ss.ms_eqv (MS X F pc fc None m ro) (MS R F pc fc None m ro).
Proof. intros X R F pc fc m ro H. split; [exact H|]. repeat split; reflexivity. Qed.

(* ==========================================================================
   3. The slot's blocks hb
   ========================================================================== *)

Lemma g0_hb_bytes_perm : forall h h', Permutation h h' -> hb_bytes h = hb_bytes h'.
Proof.
  intros h h' HP. induction HP as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; rewrite ?hb_bytes_cons.
  - reflexivity.
  - rewrite IH. reflexivity.
  - ring.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma g0_room0 : forall g E hb T, hb_inv g E hb T -> (T = [] \/ exists f, T = [(f, MF_BLOCK)]) ->
  (length hb <= 3)%nat /\ 0 <= hb_bytes hb <= 10676.
Proof.
  intros g E hb T HI HT. unfold hb_inv in HI.
  rewrite (Permutation_length HI), (g0_hb_bytes_perm _ _ HI).
  unfold hx. destruct (lg_T g) as [|t l];
    destruct HT as [-> | (f & ->)]; cbn; unfold MD_SIZE, MK_SIZE, MF_BLOCK; lia.
Qed.

Lemma g0_room : forall hb, (length hb <= 3)%nat -> 0 <= hb_bytes hb <= 10676 -> lroom_hb hb.
Proof. intros hb H1 H2. unfold lroom_hb. split; lia. Qed.

Lemma g0_room_opt : forall hb a n, (length hb <= 3)%nat -> 0 <= hb_bytes hb <= 10676 -> 0 <= n <= 40 ->
  lroom_hb (opt_hb a n hb).
Proof.
  intros hb a n H1 H2 Hn. unfold lroom_hb, opt_hb. destruct (a =? 0).
  - split; lia.
  - cbn [length]. rewrite hb_bytes_cons. cbn [snd]. split; lia.
Qed.

Lemma g0_opt0 : forall n hb, opt_hb 0 n hb = hb.
Proof. intros n hb. reflexivity. Qed.

Lemma g0_opt_nz : forall a n hb, a <> 0 -> opt_hb a n hb = (a, n) :: hb.
Proof. intros a n hb H. unfold opt_hb. destruct (Z.eqb_spec a 0); [contradiction | reflexivity]. Qed.

Lemma g0_opt_cons : forall a n x hb, opt_hb a n (x :: hb) = opt_hb a n [] ++ x :: hb.
Proof. intros a n x hb. unfold opt_hb. destruct (a =? 0); reflexivity. Qed.

Lemma g0_opt_app : forall a n hb, opt_hb a n [] ++ hb = opt_hb a n hb.
Proof. intros a n hb. unfold opt_hb. destruct (a =? 0); reflexivity. Qed.

Lemma g0_in_opt : forall t a n hb, In t hb -> In t (opt_hb a n hb).
Proof. intros t a n hb H. unfold opt_hb. destruct (a =? 0); [exact H | right; exact H]. Qed.

Lemma g0_in_opt_self : forall a n hb, a <> 0 -> In (a, n) (opt_hb a n hb).
Proof. intros a n hb H. rewrite (g0_opt_nz a n hb H). left. reflexivity. Qed.

Lemma g0_in_app : forall (t : Z * Z) l1 l2, In t l2 -> In t (l1 ++ l2).
Proof. intros t l1 l2 H. apply in_or_app. right. exact H. Qed.

Lemma g0_notT : forall (T : list (Z * Z)) (a n : Z), (T = [] \/ exists f, T = [(f, MF_BLOCK)]) -> n < MF_BLOCK ->
  ~ In (a, n) T.
Proof.
  intros T a n HT Hn. destruct HT as [-> | (f & ->)]; [intros [] |]. intros [Hf | []].
  injection Hf as _ Hs. lia.
Qed.

(* the hp side condition of cut_evt for the arm's text_buf blocks *)
Lemma g0_hp_opt : forall hp hb T cap a, (forall t, In t hp -> In t hb /\ ~ In t T) ->
  (T = [] \/ exists f, T = [(f, MF_BLOCK)]) -> 0 <= cap < 40 -> (cap <> 0 -> a <> 0) ->
  forall t, In t (hp ++ c0_opt cap a) -> In t (opt_hb a (cap + 1) hb) /\ ~ In t T.
Proof.
  intros hp hb T cap a H HT Hc Ha t Ht. apply in_app_or in Ht as [Ht|Ht].
  - destruct (H t Ht) as [H1 H2]. split; [exact (g0_in_opt t a (cap + 1) hb H1) | exact H2].
  - revert Ht. unfold c0_opt. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; [intros []|].
    intros [<- | []]. split.
    + exact (g0_in_opt_self a (cap + 1) hb (Ha Hc0)).
    + apply (g0_notT T a (cap + 1) HT). unfold MF_BLOCK. lia.
Qed.

(* ==========================================================================
   4. Memory: the arm's facts across an allocator call
   ========================================================================== *)

Lemma g0_cells_size : forall md mk P N j0 wa wk j2,
  Z.of_nat (cells_size (c0_cells md mk P N j0 wa wk j2)) = 376.
Proof. reflexivity. Qed.

Lemma g0_frame_carry : forall E P N wa wk m m',
  c0_frame E P N wa wk m -> lcarry (lh_reg E) m m' -> c0_frame E P N wa wk m'.
Proof.
  intros E P N wa wk m m' (j0 & j2 & Fr) C. exists j0, j2.
  apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact Fr].
  intros x Hx. apply lh_reg_frame. rewrite g0_cells_size in Hx. unfold lo_rng, SLOT_FRAME in *. lia.
Qed.

Lemma g0_base_carry : forall E P N kbs mbs gbs m m',
  c0_base E P N kbs mbs gbs m -> lcarry (lh_reg E) m m' ->
  wr_at rsegs m' A_ERRNO 4 -> guard_m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  c0_base E P N kbs mbs gbs m'.
Proof.
  intros E P N kbs mbs gbs m m' H C Hw Hg Hmi Htm Hst.
  destruct H as (Sv & Nk & Nw & It & No & Nm & Gn & Od & Po & La & Tx & Ip & Md & Mw & Mk & Kw & Ma & Cu & _).
  assert (Sv' : bytes_at rsegs m' (e_S E - 104) (e_saved E)).
  { apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact Sv]. intros x Hx. apply lh_reg_saved. exact Hx. }
  assert (Nk' : nlk_at m' kbs).
  { apply (ml_use _ _ _ m m' (ml_nlk_at kbs) C); [|exact Nk]. intros x Hx. apply lh_reg_gnl. exact Hx. }
  assert (ItIp : iftab_at m' kbs link_tab /\ ifptrs_at m').
  { apply (ml_use _ _ _ m m' (ml_iftab kbs) C); [|exact (conj It Ip)]. exact (lo_iftab_lh E). }
  destruct ItIp as [It' Ip'].
  assert (Gn' : gnames_at m').
  { apply (ml_use _ _ _ m m' ml_gnames_at C); [|exact Gn]. intros x Hx. apply lh_reg_gnames. exact Hx. }
  assert (Od' : odd_at m').
  { apply (ml_use _ _ _ m m' ml_odd_at C); [|exact Od].
    intros x [Hx|Hx]; [apply lh_reg_oddtab | apply lh_reg_oddstr]; exact Hx. }
  assert (Po' : policy_ro m').
  { apply (ml_use _ _ _ m m' ml_policy_ro C); [|exact Po]. intros x Hx. apply lh_reg_pol. exact Hx. }
  assert (La' : la_ok m').
  { apply (ml_use _ _ _ m m' ml_la_ok C); [|exact La]. intros x Hx. apply lh_reg_la. exact Hx. }
  assert (Tx' : texts_at m').
  { apply (ml_use _ _ _ m m' ml_texts_at C); [|exact Tx]. intros x Hx. apply lh_reg_texts. exact Hx. }
  assert (Md' : model_at m' (e_md E) mbs).
  { apply (ml_use _ _ _ m m' (ml_model_at _ _) C); [|exact Md]. intros x Hx. apply lh_reg_md. exact Hx. }
  assert (Mk' : marks_at m' (e_mk E) gbs).
  { apply (ml_use _ _ _ m m' (ml_marks_at _ _) C); [|exact Mk]. intros x Hx. apply lh_reg_mk. exact Hx. }
  assert (Cu' : cursor_ok m' (e_p0 E) (e_pl E) P N).
  { apply (ml_use _ _ _ m m' (ml_cursor_ok _ _ _ _) C); [|exact Cu]. intros x Hx. apply lh_reg_pl. exact Hx. }
  exact (conj Sv' (conj Nk' (conj Nw (conj It' (conj No (conj Nm (conj Gn' (conj Od' (conj Po' (conj La'
    (conj Tx' (conj Ip' (conj Md' (conj Mw (conj Mk' (conj Kw (conj Ma (conj Cu' (conj Hw (conj Hg
    (conj Hmi (conj Htm Hst)))))))))))))))))))))).
Qed.

Section G0L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

(* ---- CUT bookkeeping ---- *)

Lemma g0_cut_ex : forall (X : Type) g pc hb T (Q : X -> machine_state -> Prop) c,
  CUT B API g pc hb T (fun ms => exists x, Q x ms) c -> exists x, CUT B API g pc hb T (Q x) c.
Proof using B API FF.
  intros X g pc hb T Q c (fx' & L & A & regs & mem & md & E & Hf & HL & (c0 & (x & HQ) & Heq)).
  exists x. exists fx', L, A, regs, mem, md. split; [exact E|]. split; [exact Hf|]. split; [exact HL|].
  exists c0. split; [exact HQ | exact Heq].
Qed.

Lemma g0_cut_cl : forall g pc hb T (Q : machine_state -> Prop) c,
  CUT B API g pc hb T (eqv_cl Q) c -> CUT B API g pc hb T Q c.
Proof using B API FF.
  intros g pc hb T Q c (fx' & L & A & regs & mem & md & E & Hf & HL & H).
  exists fx', L, A, regs, mem, md. split; [exact E|]. split; [exact Hf|]. split; [exact HL|].
  exact (c45_eqv_cl_idem Q _ H).
Qed.

Lemma g0_cut_pure : forall g pc hb T (P : machine_state -> Prop) (Q : Prop) c,
  CUT B API g pc hb T P c -> (forall ms, P ms -> Q) -> Q.
Proof using B API FF.
  intros g pc hb T P Q c (fx' & L & A & regs & mem & md & _ & _ & _ & (c0 & HP & _)) K. exact (K c0 HP).
Qed.

(* ---- the payload is an entry block ---- *)

Lemma g0_pl_blocks : forall g md mk, LGV B API g -> lenv_ok (lg_E g md mk) ->
  In (e_p0 (lg_E g md mk), Z.of_nat (length (e_pl (lg_E g md mk)))) (blocks (lg_L g) (lg_A g)).
Proof using B API FF.
  intros g md mk HV HE.
  pose proof (len_ghost_ok B API FF g HV) as (_ & _ & _ & Hn & _ & Hpl).
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  change (e_p0 (lg_E g md mk)) with (len_p0 g). change (e_pl (lg_E g md mk)) with (lg_pl g) in HL |- *.
  rewrite <- Hn in HL |- *. destruct (Hpl ltac:(lia)) as [Hp _]. rewrite Hp.
  destruct HV as ((Hpre & _) & _).
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcase & _).
  destruct Hcase as [(Hn0 & _) | (Hn0 & q & Hq & Hp')]; [lia|].
  unfold blocks. apply in_map_iff. exists (q, lg_n g). cbn [fst snd]. rewrite Hp'. split; [reflexivity | exact Hq].
Qed.

Lemma g0_pl_in : forall g md mk, LGV B API g -> lenv_ok (lg_E g md mk) ->
  forall y, e_p0 (lg_E g md mk) <= y < e_p0 (lg_E g md mk) + Z.of_nat (length (e_pl (lg_E g md mk))) ->
  in_blk0 g y.
Proof using B API FF.
  intros g md mk HV HE y Hy. exists (e_p0 (lg_E g md mk)), (Z.of_nat (length (e_pl (lg_E g md mk)))).
  split; [exact (g0_pl_blocks g md mk HV HE) | exact Hy].
Qed.

Lemma g0_keep_lh : forall g md mk hb m m', LGV B API g -> lenv_ok (lg_E g md mk) ->
  In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb -> lcarry (lkeep B g hb) m m' -> lcarry (lh_reg (lg_E g md mk)) m m'.
Proof using B API FF.
  intros g md mk hb m m' HV HE Hmd Hmk C. apply (lcarry_mono _ (lkeep B g hb)); [|exact C].
  intros x Hx. exact (lh_reg_keep_ok B API SH SK g hb (lg_E g md mk) x FF HE eq_refl Hmd Hmk
                        (g0_pl_in g md mk HV HE) Hx).
Qed.

(* ---- the arm's memory facts after an allocator call ---- *)

Lemma g0_post_carry : forall g md mk hb P N wa wk kbs mbs gbs m m', LGV B API g -> lenv_ok (lg_E g md mk) ->
  In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb ->
  c0_frame (lg_E g md mk) P N wa wk m -> c0_base (lg_E g md mk) P N kbs mbs gbs m ->
  lcarry (lkeep B g hb) m m' -> lpost_mem g m' ->
  c0_frame (lg_E g md mk) P N wa wk m' /\ c0_base (lg_E g md mk) P N kbs mbs gbs m'.
Proof using B API FF.
  intros g md mk hb P N wa wk kbs mbs gbs m m' HV HE Hmd Hmk HF HB C (MI & TM & ST & ER & GD).
  pose proof (g0_keep_lh g md mk hb m m' HV HE Hmd Hmk C) as CL.
  split; [exact (g0_frame_carry _ _ _ _ _ m m' HF CL)|].
  exact (g0_base_carry _ _ _ _ _ _ m m' HB CL ER GD MI TM ST).
Qed.

Lemma g0_tbuf_carry : forall g hb a cap bs m m', 0 <= cap -> In (a, cap + 1) hb ->
  tbuf_at m a cap bs -> lcarry (lkeep B g hb) m m' -> tbuf_at m' a cap bs.
Proof using B API FF.
  intros g hb a cap bs m m' Hc Hin Ht C. apply (ml_use _ _ _ m m' (ml_tbuf_at a cap bs) C); [|exact Ht].
  intros x Hx. unfold lo_rng in Hx. right; right; left. exists a, (cap + 1). split; [exact Hin | lia].
Qed.

(* ---- a fresh text_buf block is an arm block ---- *)

Lemma g0_blk : forall g md mk hb r n, LGV B API g -> lenv_ok (lg_E g md mk) ->
  In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb -> lfresh B g hb r n -> c0_blk (lg_E g md mk) r n.
Proof using B API FF.
  intros g md mk hb r n HV HE Hmd Hmk (_ & Hr1 & Hr2 & Himg & Hhb & Hb0).
  split; [split; [exact Hr1 | split]|].
  - unfold SLOT_STACK in Hr2. change (e_S (lg_E g md mk)) with (lg_S g). unfold SLOT_STACK_Z. lia.
  - intros j Hj s Hs Hrng. apply (Himg j Hj). unfold in_img. rewrite (lff_segs B API FF).
    split; [exact lfr_rsegs_nonnil | exists s; split; [exact Hs | exact Hrng]].
  - split; [exact (Hhb _ _ Hmd)|]. split; [exact (Hhb _ _ Hmk)|].
    exact (Hb0 _ _ (g0_pl_blocks g md mk HV HE)).
Qed.

End G0L.
