(* The slot LLVMFuzzerTestOneInput, plain image: segment A of the op_write arm (fuzz_link.c:735-751),
   from the loop head (0x13a1c, LDefs.lh_ms) to the call of text_of (0x13fb4, entry 0x15aa8, ra 0x13fb8,
   LC1Defs.c1_15aa8). The segment calls no function.

   The code (link/ct/dis/plain/LLVMFuzzerTestOneInput.s):
   - 0x13a1c-0x13a64, the dispatch: a2 = in.p (sp + 0x40), a3 = the op byte b = *in.p, b % 6 by the
     multiply 0xab (LC1ALib.c1a_opx_val: 1, from lh_op), in.p = p + 1 and in.n = n - 1 stored
     (sp + 0x40, sp + 0x48), the jump table 0x106b0 (.rodata, entry 1 = 0x351c) -> 0x13bcc;
   - 0x13bcc-0x13d18 and 0x13f80-0x13fa8, the inlined name_of: with n = 1 the selector is 0 and the
     cursor stays (p + 1, 0); else the selector nb = p[1], in.p = p + 2, in.n = n - 2 stored again, and
     s2 = 0 (nb = 0xff), g_names + 8 nb (nb <= 63), or odd[nb % 6] (mulhu by 0x2aaaaaaaaaaaaaab,
     LC1ALib.c1a_m6x_val); in each case s2 = LDefs.sel_ptr nb;
   - 0x13fac-0x13fb4: a0 = sp + 0x40, a1 = sp + 0x78, jal text_of.
   The only stores are the two cursor cells, inside the slot's frame (LC1ALib.c1a_W), so lh_mem carries
   over (LC1ALib.c1a_lh_mem_move) and the footprint is in own_w's stack window (LC1ALib.c1a_seg_fp). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call LC1ALib.
Import ListNotations.
Local Open Scope Z_scope.

(* the value of register k in the walk's current state *)
Ltac c1a_get_reg k :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
      let v := eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end) in v
  end.
Ltac c1a_rep_reg k t tac := let v := c1a_get_reg k in replace v with t by tac.

(* a branch condition over words whose values lia bounds *)
Ltac c1a_cond := unfold_cond; cbv delta [zxb]; fold_lit_ux; repeat (rewrite unsigned_lit by lia); solve_cond_rec.
Ltac c1a_if_true :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota | symmetry; c1a_cond]
  end.
Ltac c1a_if_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota | symmetry; c1a_cond]
  end.

(* the post of segment A over the loop head's memory m0 *)
Definition c1a_post (E : lenv) (i : Z) (gp : word) (m0 : word -> option byte) (ms' : machine_state) : Prop :=
  c1_15aa8 E i gp ms' /\ seg_fp (e_S E) (c1_hp E) m0 (ms_mem ms').

(* the state at the call of text_of satisfies the post *)
Lemma c1a_close : forall (E : lenv) (i : Z) (gp : word) (m0 m : word -> option byte)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (P N P' N' nb : Z) (kbs mbs gbs j0 j1 j2 : list byte) (w1 w2 w3 w4 w5 w6 w7 : word),
  lenv_ok E -> frm0 fc -> 0 <= i <= 47 -> 0 <= nb < 256 ->
  lh_mem E i P N kbs mbs gbs m0 ->
  munch (c1a_W E) m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (e_S E - SLOT_FRAME)
    [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 (Z_to_bv 64 P'); C8 (Z_to_bv 64 N');
     CB 40 j1; CB 256 j2] ->
  (exists k, 0 <= k <= Z.of_nat (length (e_pl E)) /\ P' = e_p0 E + k /\ N' = Z.of_nat (length (e_pl E)) - k) ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m0 -> stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  c1a_post E i gp m0
    (MS (mkR (wz C1_TEXT_OF_RA) (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
             (wz (e_S E - SLOT_FRAME + FO_P)) (wz (e_S E - SLOT_FRAME + FO_B256)) a2 a3 a4 a5 a6 a7
             (wz (sel_ptr nb)) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
             (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
        F (wz C1_TEXT_OF) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp m0 m t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 F fc P N P' N' nb kbs mbs gbs j0 j1 j2
    w1 w2 w3 w4 w5 w6 w7 HE FRM Hi Hnb HLM MU WM HF HK MI TM STK.
  apply c1a_frame_split in HF. destruct HF as (_ & HC & _).
  pose proof HK as (k & Hk & _ & HNk).
  pose proof HE as (_ & HS2 & _).
  unfold c1a_post. split.
  - unfold c1_15aa8.
    exists t0, t1, t2, a2, a3, a4, a5, a6, a7, s3, s4, t3, t4, t5, t6, F, fc, m, P', N', kbs, mbs, gbs, nb.
    split; [reflexivity|].
    split; [exact FRM|]. split; [exact Hi|]. split; [exact Hnb|]. split; [lia|].
    split; [exact (c1a_lh_mem_move E i P N P' N' kbs mbs gbs m0 m HE HLM MU WM HC HK)|].
    split; [exact HC|]. split; [exact MI|]. split; [exact (c1a_task E m0 m TM MU HS2) | exact STK].
  - exact (c1a_seg_fp E m0 m MU WM).
Qed.

Ltac c1a_fin k :=
  apply evt_eqv_done;
  eapply c1a_close; try eassumption; first [lia | exists k; lia].

(* the walk from the loop head, with lh_op's facts *)
Lemma c1a_walk : forall (E : lenv) (i : Z) (gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P N P1 : Z) (kbs mbs gbs : list byte) (b : byte),
  lenv_ok E -> frm0 fc -> 0 <= i <= 47 -> 1 <= N -> lh_mem E i P N kbs mbs gbs m ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  bytes_at rsegs m (e_S E - SLOT_FRAME + FO_P) (le8 (wz P1)) -> bytes_at rsegs m P1 [b] -> bz b mod 6 = 1 ->
  evt rsegs (eqv_cl (c1a_post E i gp m))
    (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40) a0 a1 a2 a3 a4 a5 a6 a7
             (wz N) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i)
             t3 t4 t5 t6)
        F (wz L_LH) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 F fc m P N P1 kbs mbs gbs b
    HE FRM Hi HN HLM MI TM STK HP1 Hb Hop.
  pose proof HLM as ((j0 & j1 & j2 & nc & HF) & _ & _ & _ & _ & _ & _ & _ & _ & _ & HODD & _ & _ & _ & _ & _ & _ &
                     _ & _ & _ & (HPL & k & Hk & HPk & HNk) & _ & _).
  pose proof HE as (HS1 & HS2 & HS3 & _ & _ & _ & _ & _ & Hpl & (Hp0a & Hp0b & _) & _).
  assert (ESZ : SLOT_STACK_Z = 65536) by reflexivity.
  assert (ESF : SLOT_FRAME = 480) by reflexivity.
  assert (EP1 : P1 = P) by (eapply c1a_cur_eq; [exact HLM | exact HP1 | exact Hb | lia]).
  subst P1. clear HP1.
  pose proof (c1a_odd_ro m HODD) as HOT. clear HODD. unfold c1a_odd_cells in HOT.
  pose proof (c1a_ov1 m P b Hb) as HR.
  unfold lh_cells, wz, A_ODD, A_G_NAMES, A_JT, GNL42, GNL40, A_G_NL, A_EMPTY, MD_MARK in HF.
  unfold wz, A_TP, GNL40, A_G_NL, A_JT, L_LH, MD_N_REQ.
  pose proof (munch_refl [(e_S E - SLOT_FRAME + 64, e_S E - SLOT_FRAME + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x13a1c-0x13a44: the op byte and b % 6 *)
  do 11 step.
  c1a_rep_reg 13 (Z_to_bv 64 1) ltac:(symmetry; exact (c1a_opx_val b Hop)).
  (* 0x13a48-0x13a50: the cursor (p + 1, n - 1); op 1 <= 4 *)
  do 3 step. c1a_if_false.
  (* 0x13a54-0x13a64: the jump table -> 0x13bcc; beqz a1 *)
  do 6 step.
  destruct (Z.eq_dec N 1) as [N1|N2].
  - (* n = 1: selector 0, s2 = g_names *)
    c1a_if_true. do 9 step.
    c1a_rep_reg 18 (wz (sel_ptr 0)) ltac:(reflexivity).
    c1a_fin (k + 1).
  - (* the selector byte nb = p[1]; the cursor (p + 2, n - 2) *)
    c1a_if_false.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : bytes_at rsegs mm (e_p0 E) (e_pl E) |- _ =>
        destruct (c1a_pl_byte mm (e_p0 E) (e_pl E) (k + 1) H ltac:(lia)) as (nbb & _ & HR1) end end.
    replace (e_p0 E + (k + 1)) with (P + 1) in HR1 by lia.
    pose proof (c1a_bz_range nbb) as Rnb. unfold bz in Rnb.
    do 7 step.
    destruct (Z.eq_dec (bv_unsigned nbb) 255) as [B255|B255].
    + (* nb = 0xff: s2 = NULL *)
      c1a_if_false. do 5 step.
      c1a_rep_reg 18 (wz (sel_ptr (bz nbb))) ltac:(unfold sel_ptr, bz; rewrite B255; reflexivity).
      c1a_fin (k + 2).
    + c1a_if_true. do 2 step.
      destruct (Z_lt_le_dec 63 (bv_unsigned nbb)) as [BH|BL].
      * (* nb >= 64: s2 = odd[nb % 6] *)
        c1a_if_true. do 7 step.
        c1a_rep_reg 10 (Z_to_bv 64 (bz nbb mod 6)) ltac:(symmetry; exact (c1a_m6x_val nbb)).
        pose proof (Z.mod_pos_bound (bz nbb) 6 ltac:(lia)) as Hr.
        assert (Esel : forall r, bz nbb mod 6 = r -> sel_ptr (bz nbb) = nth (Z.to_nat r) odd_ptrs 0).
        { intros r Er. unfold sel_ptr.
          rewrite (proj2 (Z.eqb_neq _ _)) by (unfold bz; lia).
          rewrite (proj2 (Z.ltb_ge _ _)) by (unfold bz; lia).
          rewrite Er. reflexivity. }
        destruct (c1a_six _ Hr) as [R|[R|[R|[R|[R|R]]]]]; rewrite R; do 7 step;
          c1a_rep_reg 18 (wz (sel_ptr (bz nbb))) ltac:(rewrite (Esel _ R); reflexivity);
          c1a_fin (k + 2).
      * (* nb <= 63: s2 = g_names + 8 nb *)
        c1a_if_false. do 7 step.
        c1a_rep_reg 18 (wz (sel_ptr (bz nbb)))
          ltac:(unfold sel_ptr, bz;
                rewrite (proj2 (Z.eqb_neq _ _)) by lia; rewrite (proj2 (Z.ltb_lt _ _)) by lia;
                unfold wz, zxb, A_G_NAMES; rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia;
                change (2 ^ 3) with 8; f_equal; lia).
        c1a_fin (k + 2).
Qed.

(* Segment A of op_write: from the loop head of operation i whose op byte is 1 mod 6, to the call of
   text_of (LC1Defs.c1_15aa8), writing only the cursor cells. *)
Theorem c1_seg_A : forall (E : lenv) (i : Z) (gp : word) (ms : machine_state),
  lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 1 ->
  evt rsegs (eqv_cl (fun ms' => c1_15aa8 E i gp ms' /\ seg_fp (e_S E) (c1_hp E) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp ms HE HL HO.
  destruct HL as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 &
                  F & fc & m & P & N & kbs & mbs & gbs & -> & FRM & Hi & HN & HLM & MI & TM & STK).
  destruct HO as (P1 & b & HP1 & Hb & Hop).
  exact (c1a_walk E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 F fc m P N P1 kbs mbs gbs b
           HE FRM Hi HN HLM MI TM STK HP1 Hb Hop).
Qed.
