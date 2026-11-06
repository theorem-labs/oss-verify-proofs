(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Prog/pod_nearest.v at ca77675ebeb; the walk ported to image A's pod_nearest 0x82ccc (fuzz_role.asan): frame 0x40 with s4, the .got / shadow-cell loads and the instrumented check before the store of r. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgNearW.v at 92636bfca57b; the module paths name reac-pw/fuzz_rate, and the walk is taken at reac-pw/fuzz_rate's image A (fuzz_rate.asan): entry 0x83dc0 (was 0x82ccc), pcs +0x10f4, the .got slot 0x9be70 (was 0x9a830), the shadow-offset cell 0xa4c38 (was 0xa33f8), the callees __extendsftf2 0x84cec, __lttf2 0x849d8, __floatditf 0x84e48, __subtf3 0x84f6c, __getf2 0x84aa0. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgNearW.v at b089f28d962e; the walk is taken at reac-pw/fuzz_rate's image B (fuzz_rate.asan-ubsan, lib/AU/Img0.v): every address is lib/AU/RtPgNearImgB.v's and every pc an offset from its entry, the five soft-float callee contracts at image B's symbol map are Section hypotheses, and the five trap steps (two conversion checks with the one more __getf2 call, the two overflow checks on t + 1 and t - 1 with lts_inc and lts_dec, the alignment check of out) are taken from proofs/reac-pw/fuzz_rate/lib/U/Prog/pod_nearest.v at 09704c734de1. *)
(** pod_nearest of fuzz_rate's ASan image B (fuzz_rate.asan-ubsan, entry E = RtPgNearImgB.B_POD_NEAREST, 384 bytes,
    96 instructions): proof of lib/AU/RtPgNearCB.v's [pod_nearest_B_contract] from the binary128 value facts
    [near_sf_facts] and the contracts of the five soft-float callees at image B's symbol map RtPgNearImgB.N_img.

    The value half is the plain build's (lib/Prog/pod_nearest.v: [pn_bin], [pn_bin_nearest], [pn_traps]); so are the
    callee bridges [br_ext], [br_le], [br_ge], [br_fd], [br_sub] (parametric in the image record), the register
    lemmas and the tactics. The walk is image A's walk (lib/A/RtPgNearW.v) with image B's changes:
      - the frame is 0x40 bytes: ra, s0-s4 and fs0 in the 56 bytes [sp - 56, sp) ([frm4]); the 8 bytes
        [sp - 64, sp - 56) are not written; __addtf3's 48 bytes are [sp - 112, sp - 64) ([frm_stk], [frm_sub]);
        nothing outside the 112 bytes below sp changes before the store of r ([frm]);
      - E+0x30-E+0x38 load the .got slot B_GOT_SHADOW (the address B_SHADOW_CELL of the shadow-offset cell) and
        that cell (0x7fff8000) into s4 ([frm_got], [frm_cell]: both cells lie below the stack window, so the frame
        stores and the callees leave them as they were);
      - E+0x7c-E+0xa8, after the range test, the two checks of (long long)d branch to the trap `unimp` E+0x174 when
        f >= 2^63 or __getf2(d, -2^63 - 1) <= 0: [pn_traps] gives f < 2^63 and d > -2^63 - 1, so neither is taken
        (the steps of lib/U/Prog/pod_nearest.v's checks 1 and 2);
      - E+0x104 and E+0x110 form t - 1 and t + 1 in a0 and branch to the trap when the result is not below
        (above) t; [pn_traps] bounds t to [-2^31 - 1, 2^31], so neither is taken ([lts_dec], [lts_inc]);
      - E+0x12c, before the instrumented check, `andi a0,s0,7; bnez` branches to the trap; out mod 8 = 0;
      - E+0x134-E+0x140, before the store of r at out, the instrumented check loads the shadow byte at
        (out >> 3) + 0x7fff8000; that byte lies outside the 112 bytes below sp, so it is still 0 ([frm_sh]), and
        the branch to the error path E+0x178 is not taken;
      - the shared exit E+0x14c restores s4 too ([epi]). *)
From Stdlib Require Import ZArith NArith List Lia Bool SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import pod_nearest.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require C_extendsftf2 C_floatditf G_letf2 G_getf2 G_subtf3.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgNearImgB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgNearCB.
Import ListNotations.
Open Scope Z_scope.

Module NI := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.RtPgNearImgB.

(** fcvt.l.s, as the plain walk steps it (a Local override there, so repeated here). *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib.Step.exec_pre i ::=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fcvt FC_L FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_s sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | _ => idtac
    end
  end;
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

(** ** Reads of cells whose bytes are known *)
Lemma rd8_of : forall segs m A (v : word), bytes_at segs m A (le8 v) ->
  ov_read_bytes segs m (Z_to_bv 64 A) 8 = Some (le8 v).
Proof.
  intros segs m A v H.
  pose proof (bytes_at_ov_read segs m A (le8 v) 0 8 H ltac:(rewrite length_le8; lia)) as R.
  replace (A + Z.of_nat 0) with A in R by lia.
  exact R.
Qed.

Lemma rd1_of : forall segs m A (x : byte), bytes_at segs m A [x] ->
  ov_read_bytes segs m (Z_to_bv 64 A) 1 = Some [x].
Proof.
  intros segs m A x H.
  pose proof (bytes_at_read segs m A [x] 0 1 H ltac:(lia) ltac:(cbn; lia)) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.

(** The address the instrumented check forms from s0 = out: `srli a0,s0,3; add a0,a0,s4` with s4 = 0x7fff8000. *)
Lemma sh_addr : forall o, 0 <= o < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 o)) 3 + 0x7fff8000)) = 0x7fff8000 + o / 8.
Proof.
  intros o Ho. rewrite (unsigned_lit o) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (H1 : 0 <= o / 8) by (apply Z.div_pos; lia).
  assert (H2 : o / 8 < 2^61) by (apply Z.div_lt_upper_bound; lia).
  rewrite unsigned_lit by lia. lia.
Qed.

(** A load whose address is the shadow byte's: [HR] gives its bytes at every word with that unsigned value. *)
Ltac solve_load_sh :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    match goal with
    | HR : forall a' : word, bv_unsigned a' = _ -> ov_read_bytes segs m a' n = Some _ |- _ =>
        rewrite (HR a) by (apply sh_addr; lia);
        load_post
    end
  end.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib.Step.solve_load ::=
  first [ solve_load_base | solve_load_image | solve_load_sh ].

(** The overflow checks on t + 1 and t - 1 (`addi a0,s1,+-1`, `blt a0,s1`), as lib/U/Prog/pod_nearest.v
    states them. *)
Lemma lts_inc : forall t, -2^31 - 1 <= bv_swrap 64 t <= 2^31 ->
  bv_lts (Z_to_bv 64 (t + 1)) (Z_to_bv 64 t) = false.
Proof.
  intros t Ht. unfold bv_lts. rewrite !zb_signed, !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap in Ht. change (bv_half_modulus 64) with (2^63) in Ht.
  change (bv_modulus 64) with (2^64) in Ht.
  apply Z.ltb_ge.
  destruct (Z.ltb_spec ((t + 1) mod 2^64) (2^63)); destruct (Z.ltb_spec (t mod 2^64) (2^63)); cbv iota;
    revert Ht; Z.div_mod_to_equations; lia.
Qed.

Lemma lts_dec : forall t, -2^31 - 1 <= bv_swrap 64 t <= 2^31 ->
  bv_lts (Z_to_bv 64 (t + -1)) (Z_to_bv 64 t) = true.
Proof.
  intros t Ht. unfold bv_lts. rewrite !zb_signed, !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap in Ht. change (bv_half_modulus 64) with (2^63) in Ht.
  change (bv_modulus 64) with (2^64) in Ht.
  apply Z.ltb_lt.
  destruct (Z.ltb_spec ((t + -1) mod 2^64) (2^63)); destruct (Z.ltb_spec (t mod 2^64) (2^63)); cbv iota;
    revert Ht; Z.div_mod_to_equations; lia.
Qed.

(** The goal's pc, written as an offset from the entry, read as one numeral. *)
Ltac lit_pc :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => let v := eval vm_compute in p in change p with v
  end.

Section Walk.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m0 : word -> option byte)
  (b Sp out lo : Z).
Hypothesis NS : near_sf_facts.
Hypothesis HEX : @C_extendsftf2.extendsftf2_contract NI.N_img.
Hypothesis HLE : @G_letf2.letf2_contract NI.N_img.
Hypothesis HFD : @C_floatditf.floatditf_contract NI.N_img.
Hypothesis HSB : @G_subtf3.subtf3_contract NI.N_img.
Hypothesis HGE : @G_getf2.getf2_contract NI.N_img.
Hypothesis Hb : 0 <= b < 2^32.
Hypothesis HF10 : Sem.reg_get F (Z_to_bv 5 10) = nan_box (Z_to_bv 32 b).
Hypothesis Hout : 0 <= out /\ out + 8 <= 2^64.
Hypothesis Hal : out mod 8 = 0.
Hypothesis Hdj : hold (out + 8 <= Sp - 112 \/ Sp <= out).
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 112 <= Sp.
Hypothesis HSp : Sp <= 2^64.
Hypothesis HLO : NI.B_SHADOW_CELL + 8 <= lo.
Hypothesis HGOT : hold (bytes_at rsegs m0 NI.B_GOT_SHADOW (le8 (Z_to_bv 64 NI.B_SHADOW_CELL))).
Hypothesis HCELL : hold (bytes_at rsegs m0 NI.B_SHADOW_CELL (le8 (Z_to_bv 64 0x7fff8000))).
Hypothesis HSH : hold (bytes_at rsegs m0 (0x7fff8000 + out / 8) [Z_to_bv 8 0]).
Hypothesis HSHo : hold (outside [(Sp - 112, Sp)] (0x7fff8000 + out / 8)).
Hypothesis TM0 : MemNorm.task_mem rsegs m0.
Hypothesis WR0 : forall a : word, Sp - 112 <= bv_unsigned a < Sp \/ out <= bv_unsigned a < out + 8 ->
  wview rsegs m0 a <> None.

(** The contract's post, with the machine model [pn_bin] in place of [nearest]. *)
Definition Post : machine_state -> Prop := fun ms' =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
         (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (b_near_rc (pn_bin b)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    (forall k : bv 5, bv_unsigned k <> 15 -> Sem.reg_get F' k = Sem.reg_get F k) /\
    frm0 fc' /\
    b_near_mem m0 m' Sp out (pn_bin b) /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo Sp.

(** The frame between the prologue and the epilogue: fs0, s4, s3, s2, s1, s0, ra at [sp - 56, sp), the stack
    below it, and the facts about memory every step keeps. *)
Definition frm4 (fv : word) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (Sp + -56) [C8 fv; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (Sp + -56) /\ wmono rsegs m0 m /\ mem_inv rsegs m.
(** ... and, until the store of the result, nothing changed outside the 112 bytes below sp. *)
Definition frm (fv : word) (m : word -> option byte) : Prop := frm4 fv m /\ munch [(Sp - 112, Sp)] m0 m.

Lemma frm_mi : forall fv m, frm fv m -> mem_inv rsegs m.
Proof. intros fv m [(_ & _ & _ & MI) _]. exact MI. Qed.

Lemma tm_of : forall m, munch [(Sp - 112, Sp); (out, out + 8)] m0 m -> MemNorm.task_mem rsegs m.
Proof.
  intros m MU. apply (tm_munch rsegs _ m0 m TM0 MU). intros a Ha. apply WR0.
  cbn [outside] in Ha. lia.
Qed.

Lemma tm_frm : forall fv m, frm fv m -> MemNorm.task_mem rsegs m.
Proof.
  intros fv m [_ MU]. apply tm_of. eapply munch_weaken; [|exact MU].
  intros x Hx. cbn [outside] in *. tauto.
Qed.

(** __subtf3/__addtf3's 48 bytes, below the 8 unwritten bytes under the saved registers. *)
Lemma frm_stk : forall fv m, frm fv m -> stk rsegs m (Sp + -64 - 48) (Sp + -64).
Proof.
  intros fv m [(_ & ST & _ & _) _].
  destruct (stk_split rsegs m lo (Sp + -64 - 48) (Sp + -56) ST ltac:(lia)) as [_ S2].
  exact (proj1 (stk_split rsegs m (Sp + -64 - 48) (Sp + -64) (Sp + -56) S2 ltac:(lia))).
Qed.

(** The leaf callees write nothing. *)
Lemma frm_call : forall fv m m', frm fv m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm fv m'.
Proof.
  intros fv m m' [(FR & ST & WM & _) MU] MU' WM' MI'.
  split; [split|].
  - eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | exact I].
  - split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
    split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]; intros x _; exact I.
Qed.

(** __subtf3/__addtf3 write the 48 bytes [sp - 112, sp - 64). *)
Lemma frm_sub : forall fv m m', frm fv m -> munch [(Sp + -64 - 48, Sp + -64)] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' (Sp + -64 - 48) (Sp + -64) -> frm fv m'.
Proof.
  intros fv m m' [(FR & ST & WM & _) MU] MU' WM' MI' ST'.
  split; [split|].
  - eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |].
    cbn [disjoint_from cells_size csize]. split; [lia | exact I].
  - split.
    + destruct (stk_split rsegs m lo (Sp + -64 - 48) (Sp + -56) ST ltac:(lia)) as [STa STbc].
      destruct (stk_split rsegs m (Sp + -64 - 48) (Sp + -64) (Sp + -56) STbc ltac:(lia)) as [_ STc].
      pose proof (stk_transport_disjoint rsegs _ m m' lo (Sp + -64 - 48) STa MU' WM'
                    ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STa'.
      pose proof (stk_transport_disjoint rsegs _ m m' (Sp + -64) (Sp + -56) STc MU' WM'
                    ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STc'.
      exact (stk_merge rsegs m' lo (Sp + -64) (Sp + -56)
               (stk_merge rsegs m' lo (Sp + -64 - 48) (Sp + -64) STa' ST' ltac:(lia)) STc' ltac:(lia)).
    + split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']].
    intros x [Hx _]. split; [lia | exact I].
Qed.

(** Bytes of the entry memory outside the 112 bytes below sp are still there. *)
Lemma rd_m0 : forall fv m A bs, frm fv m -> bytes_at rsegs m0 A bs ->
  disjoint_from [(Sp - 112, Sp)] A (Z.of_nat (length bs)) -> bytes_at rsegs m A bs.
Proof. intros fv m A bs [_ MU] H D. exact (bytes_at_transport rsegs _ m0 m A bs H MU D). Qed.

(** E+0x34 `ld a0,0x174(a0)`: the .got slot holds the address of the shadow-offset cell. *)
Lemma frm_got : forall fv m, frm fv m ->
  ov_read_bytes rsegs m (Z_to_bv 64 NI.B_GOT_SHADOW) 8 = Some (le8 (Z_to_bv 64 NI.B_SHADOW_CELL)).
Proof.
  intros fv m FM. apply rd8_of. apply (rd_m0 fv m); [exact FM | exact HGOT |].
  pose proof HLO as L. unfold NI.B_SHADOW_CELL in L. unfold NI.B_GOT_SHADOW, NI.B_SHADOW_CELL.
  rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** E+0x38 `ld s4,0(a0)`: the shadow-offset cell holds 0x7fff8000. *)
Lemma frm_cell : forall fv m, frm fv m ->
  ov_read_bytes rsegs m (Z_to_bv 64 NI.B_SHADOW_CELL) 8 = Some (le8 (Z_to_bv 64 0x7fff8000)).
Proof.
  intros fv m FM. apply rd8_of. apply (rd_m0 fv m); [exact FM | exact HCELL |].
  pose proof HLO as L. unfold NI.B_SHADOW_CELL in L |- *.
  rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** E+0x13c `lbu a0,0(a0)`: the shadow byte of out is 0. *)
Lemma frm_sh : forall fv m, frm fv m -> forall a : word, bv_unsigned a = 0x7fff8000 + out / 8 ->
  ov_read_bytes rsegs m a 1 = Some [Z_to_bv 8 0].
Proof.
  intros fv m FM a Ea.
  assert (B : bytes_at rsegs m (0x7fff8000 + out / 8) [Z_to_bv 8 0]).
  { apply (rd_m0 fv m); [exact FM | exact HSH |].
    pose proof HSHo as D. unfold hold in D. cbn [outside] in D. cbn [disjoint_from length].
    split; [lia | exact I]. }
  replace a with (Z_to_bv 64 (0x7fff8000 + out / 8)) by (rewrite <- Ea; apply Z_to_bv_lit_self).
  exact (rd1_of rsegs m _ _ B).
Qed.

(** The store of the result at out (E+0x144 `sd s1,0(s0)`): out is writable (it was at the entry), outside the
    frame, and the store keeps the frame. *)
Lemma store_out : forall fv m (v : word), frm fv m ->
  frm4 fv (write_to_mem m (wa out) (le8 v)) /\
  munch [(Sp - 112, Sp); (out, out + 8)] m0 (write_to_mem m (wa out) (le8 v)) /\
  bytes_at rsegs (write_to_mem m (wa out) (le8 v)) out (le8 v) /\
  store_ok rsegs m (wa out) 8 = true.
Proof.
  intros fv m v [(FR & ST & WM & MI) MU].
  pose proof Hdj as D. unfold hold in D.
  assert (WR : wr_at rsegs m out 8).
  { split; [lia|]. split; [lia|]. intros i Hi. apply WM. apply WR0. right.
    unfold wa. rewrite unsigned_lit by lia. lia. }
  assert (HSt : store_ok rsegs m (wa out) 8 = true).
  { pose proof (wr_at_store_ok rsegs m out 8 0 8 WR ltac:(lia) ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H. }
  assert (HSt' : store_ok rsegs m (wa out) (length (le8 v)) = true) by (rewrite length_le8; exact HSt).
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + apply (rw_cells_frame rsegs m _ _ out (le8 v) FR); rewrite ?length_le8; cbn [cells_size csize]; lia.
    + apply (stk_write rsegs m lo (Sp + -56) out (le8 v) ST); rewrite ?length_le8; lia.
    + exact (wmono_write rsegs m0 m (wa out) (le8 v) WM).
    + exact (mem_inv_store rsegs m (wa out) (le8 v) MI HSt').
  - apply munch_write; rewrite ?length_le8; [| lia | lia | cbn [inside]; right; left; lia].
    eapply munch_weaken; [|exact MU]. intros x [H1 [H2 _]]. split; [exact H1 | exact I].
  - apply bytes_at_write_same; rewrite ?length_le8; lia.
  - exact HSt.
Qed.

(** The shared exit E+0x14c: a0 = s1, restore ra, s0-s4 and fs0, free the frame, return. *)
Lemma epi : forall fv (Fc : bvmap 5 word) (fc1 : bv 32) m rc
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  fv = Sem.reg_get F (Z_to_bv 5 8) ->
  (forall k : bv 5, bv_unsigned k <> 15 -> bv_unsigned k <> 8 -> Sem.reg_get Fc k = Sem.reg_get F k) ->
  frm0 fc1 -> frm4 fv m -> b_near_mem m0 m Sp out (pn_bin b) -> rc = b_near_rc (pn_bin b) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -64)) gp tp x5 x6 x7 x8 (Z_to_bv 64 rc) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        Fc (Z_to_bv 64 (NI.B_POD_NEAREST + 0x14c)) fc1 None m (seg_rom rsegs)).
Proof.
  intros fv Fc fc1 m rc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 Efv HFc FRM
    [FR [ST [WM MI]]] PM Erc.
  assert (TM : MemNorm.task_mem rsegs m).
  { apply tm_of. destruct (pn_bin b); unfold b_near_mem, B_NEAR_STACK in PM.
    - exact (proj1 PM).
    - eapply munch_weaken; [|exact PM]. intros x Hx. cbn [outside] in *. tauto. }
  lit_pc.
  do 10 step.
  match goal with |- evt _ _ (MS _ ?F' _ ?fc' _ ?m' _) =>
    apply evt_done; unfold Post;
    exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F', fc', m' end.
  split; [subst rc; unfold mkR; repeat f_equal; lia|].
  split.
  { intros k Hk. destruct (Z.eq_dec (bv_unsigned k) 8) as [E8|E8].
    - rewrite (freg_get_same Fc _ k fv) by (rewrite E8; reflexivity). rewrite Efv.
      apply reg_get_key. rewrite E8. reflexivity.
    - rewrite reg_get_set_ne by (intro E; apply E8; rewrite <- E; reflexivity). exact (HFc k Hk E8). }
  split; [exact FRM|]. split; [exact PM|]. split; [exact WM|]. split; [exact MI|]. split; [exact TM|].
  pose proof (stk_release rsegs m lo (Sp + -56) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  replace (Sp + -56 + Z.of_nat 56) with Sp in R by lia. exact R.
Qed.

(** E+0x11c: s1 = r; `sext.w a0,s1`, `beq a0,s1`: if r fits in 32 bits, the alignment check of out (E+0x12c:
    out mod 8 = 0, branch to the trap not taken), the instrumented check of out (E+0x134-E+0x140: shadow byte 0,
    branch to the error path not taken), store r at out and return 1; else return 0. *)
Lemma tail : forall fv (Fc : bvmap 5 word) (fc1 : bv 32) m (r : Z)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  fv = Sem.reg_get F (Z_to_bv 5 8) ->
  (forall k : bv 5, bv_unsigned k <> 15 -> bv_unsigned k <> 8 -> Sem.reg_get Fc k = Sem.reg_get F k) ->
  frm0 fc1 -> frm fv m ->
  pn_bin b = (if (-2^31 <=? bv_swrap 64 r) && (bv_swrap 64 r <? 2^31) then Some (bv_swrap 64 r) else None) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16
             x17 x18 x19 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        Fc (Z_to_bv 64 (NI.B_POD_NEAREST + 0x11c)) fc1 None m (seg_rom rsegs)).
Proof.
  intros fv Fc fc1 m r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 Efv HFc FRM FM Hpn.
  lit_pc.
  step. step.
  rewrite fits32.
  destruct ((-2^31 <=? bv_swrap 64 r) && (bv_swrap 64 r <? 2^31)) eqn:FIT.
  - pose proof (frm_sh _ _ FM) as HSR.
    destruct (store_out fv m (Z_to_bv 64 r) FM) as (F4 & MU2 & BY & HSt).
    cbv iota.
    (* E+0x12c andi a0,s0,7; bnez (the trap, not taken: out is 8-aligned) *)
    step. step.
    rewrite (unsigned_lit out) by lia.
    replace (Z.land out 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; symmetry; exact Hal).
    if_false.
    (* E+0x134 srli a0,s0,3; add a0,a0,s4; lbu a0,0(a0); bnez a0 (not taken) *)
    step. step. step. step. if_false.
    (* E+0x144 sd s1,0(s0); li s1,1 *)
    step. step.
    eapply epi; [exact Efv | exact HFc | exact FRM | exact F4 | |].
    + rewrite Hpn. cbn [b_near_mem]. split; [exact MU2|]. rewrite bvsw_lit. exact BY.
    + rewrite Hpn. reflexivity.
  - cbv iota. step. step.
    destruct FM as [F4 MU].
    eapply epi; [exact Efv | exact HFc | exact FRM | exact F4 | rewrite Hpn; exact MU | rewrite Hpn; reflexivity].
Qed.

Lemma body : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 -> frm0 fc ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 NI.B_POD_NEAREST) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc ST MI FRM.
  pose proof (munch_refl [(Sp - 112, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 56 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 56) with 56 in ST1, FR.
  replace (Sp - 56) with (Sp + -56) in ST1, FR by lia.
  lit_pc.
  (* prologue: the frame, ra, s0-s4 and fs0 *)
  do 8 step.
  match type of FR with rw_cells _ ?m1 _ (C8 ?v :: _) =>
    assert (FM : frm v m1) by exact (conj (conj FR (conj ST1 (conj WM MI))) MU);
    assert (Efv : v = Sem.reg_get F (Z_to_bv 5 8)) by (apply reg_get_key; reflexivity) end.
  clear FR ST1 WM MU MI.
  pose proof (frm_got _ _ FM) as HG1. pose proof (frm_cell _ _ FM) as HG2.
  unfold NI.B_GOT_SHADOW, NI.B_SHADOW_CELL in HG1, HG2.
  (* E+0x20 feq.s a1,fa0,fa0; beqz a1 *)
  step. fix_reg F HF10 10%Z. unfold feq_s. rewrite unbox_nan_box, (u32_lit b Hb).
  destruct (fst (fp_eq fmt_single b b)) eqn:FE; unfold bword; step.
  2:{ (* a NaN: E+0x124 s1 = 0, j E+0x14c: return 0 *)
      if_true. step. step.
      eapply epi; [exact Efv | intros k _ _; reflexivity | eassumption | exact (proj1 FM) | |].
      - assert (E : pn_bin b = None) by (unfold pn_bin; rewrite FE; reflexivity). rewrite E. exact (proj2 FM).
      - unfold pn_bin; rewrite FE; reflexivity. }
  if_false.
  (* E+0x28 fmv.s fs0,fa0; mv s0,a0; auipc a0,0x18; ld a0,0x174(a0) (the .got slot); ld s4,0(a0) (the
     shadow-offset cell); jal __extendsftf2 *)
  step. fix_reg F HF10 10%Z. rewrite unbox_nan_box, sgnj_self32.
  step. step. step. step.
  clear HG1 HG2.
  step.
  eapply evt_cut.
  { eapply (br_ext NI.N_img rsegs NI.B_EXTENDSFTF2 eq_refl eq_refl HEX b);
      [ rewrite freg_get_other by reflexivity; exact HF10 | exact (frm_mi _ _ FM) | exact (tm_frm _ _ FM) ]. }
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
              & MI2 & _).
  pose proof (frm_call _ _ _ FM MU2 WM2 MI2) as FM2. clear FM MU2 WM2 MI2.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* E+0x40 mv s2,a0; lui a0,0x4f000; fmv.w.x fa5,a0; flt.s a0,fa5,fs0 *)
  step. step. step. step.
  unfold flt_s. rewrite !unbox_nan_box, (u32_lit b Hb). fold_unbox.
  destruct (fst (fp_lt fmt_single 1325400064 b)) eqn:LT; unfold bword.
  { (* 2^31 < f: E+0x50 s1 = 0, bnez -> E+0x14c: return 0 *)
    step. step. if_true.
    eapply epi; [exact Efv | hfc | eassumption | exact (proj1 FM2) | |].
    - assert (E : pn_bin b = None) by (unfold pn_bin; rewrite FE, LT; reflexivity). rewrite E. exact (proj2 FM2).
    - unfold pn_bin; rewrite FE, LT; reflexivity. }
  step. step. if_false.
  (* E+0x58 mv s3,a1; a3 = high word of C1; mv a0,s2; mv a2,zero; jal __cmptf2 *)
  do 8 step.
  eapply evt_cut.
  { eapply (br_le NI.N_img rsegs NI.B_CMPTF2 eq_refl eq_refl HLE);
      [exact (frm_mi _ _ FM2) | exact (tm_frm _ _ FM2)]. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3
              & -> & MU3 & WM3 & MI3 & _).
  pose proof (frm_call _ _ _ FM2 MU3 WM3 MI3) as FM3. clear FM2 MU3 WM3 MI3.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def. fold_c128 C1_128.
  (* E+0x78 bltz a0 *)
  step. rewrite lts0 by apply f128_le_range.
  destruct (SF.f128_le (pn_d b) C1_128 <? 0) eqn:LE; cbv iota.
  { (* d < C1: -> E+0x14c with s1 = 0: return 0 *)
    eapply epi; [exact Efv | hfc | eassumption | exact (proj1 FM3) | |].
    - assert (E : pn_bin b = None) by (unfold pn_bin; rewrite FE, LT, LE; reflexivity). rewrite E. exact (proj2 FM3).
    - unfold pn_bin; rewrite FE, LT, LE; reflexivity. }
  destruct (pn_traps NS b Hb FE LT LE) as (T1 & T2 & T3).
  (* E+0x7c the first check of (long long)d: fa5 = 2^63, flt.s a0,fs0,fa5, beqz -> the trap (not taken) *)
  step. step. step.
  unfold flt_s. rewrite !unbox_nan_box, (u32_lit b Hb). fold_unbox. rewrite T1. unfold bword.
  step. if_false.
  (* E+0x8c the second check: a2:a3 = C2 = -2^63 - 1, a0:a1 = d; jal __getf2; blez -> the trap (not taken) *)
  do 7 step.
  eapply evt_cut.
  { eapply (br_ge NI.N_img rsegs NI.B_GETF2 eq_refl eq_refl HGE); [exact (frm_mi _ _ FM3) | exact (tm_frm _ _ FM3)]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU4 & WM4 & MI4 & _).
  pose proof (frm_call _ _ _ FM3 MU4 WM4 MI4) as FM4. clear FM3 MU4 WM4 MI4.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def. fold_c128 C2_128. rewrite T2.
  step. if_false.
  (* E+0xac fcvt.l.s s1,fs0,rtz *)
  step. rewrite unbox_nan_box, (u32_lit b Hb), pn_t_def.
  (* E+0xb0 mv a0,s1; jal __floatditf *)
  step. step.
  eapply evt_cut.
  { eapply (br_fd NI.N_img rsegs NI.B_FLOATDITF eq_refl eq_refl HFD (pn_t b));
      [ rewrite unsigned_lit_wrap, SF.wrap64_mod; reflexivity | exact (frm_mi _ _ FM4) | exact (tm_frm _ _ FM4) ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MU5 & WM5 & MI5 & _).
  pose proof (frm_call _ _ _ FM4 MU5 WM5 MI5) as FM5. clear FM4 MU5 WM5 MI5.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* E+0xb8 a2:a3 = (long double)t, a0:a1 = d; jal __subtf3 (sp = Sp - 64) *)
  do 5 step.
  eapply evt_cut.
  { eapply (br_sub NI.N_img rsegs NI.B_SUBTF3 eq_refl eq_refl HSB);
      [ lia | exact (frm_stk _ _ FM5) | exact (frm_mi _ _ FM5) | exact (tm_frm _ _ FM5) | eassumption ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & fc6 & m6 & -> & MU6 & WM6 & MI6 & _ & FRM6 & ST6).
  pose proof (frm_sub _ _ _ FM5 MU6 WM6 MI6 ST6) as FM6. clear FM5 MU6 WM6 MI6 ST6.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def.
  (* E+0xcc s2:s3 = frac; a2:a3 = 0.5L; jal __getf2 *)
  do 6 step.
  eapply evt_cut.
  { eapply (br_ge NI.N_img rsegs NI.B_GETF2 eq_refl eq_refl HGE);
      [exact (frm_mi _ _ FM6) | exact (tm_frm _ _ FM6)]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> & MU7 & WM7 & MI7 & _).
  pose proof (frm_call _ _ _ FM6 MU7 WM7 MI7) as FM7. clear FM6 MU7 WM7 MI7.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 HALF_128.
  (* E+0xe4 bgez a0 *)
  step. rewrite lts0 by apply f128_ge_range. rewrite Z.ltb_antisym, Bool.negb_involutive.
  destruct (0 <=? SF.f128_ge (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) HALF_128) eqn:GE;
    cbv iota.
  { (* frac >= 1/2: E+0x110 addi a0,s1,1; blt a0,s1 -> the trap (not taken: t + 1 does not overflow);
       mv s1,a0; r = t + 1 *)
    step. step. rewrite (lts_inc (pn_t b) T3). cbv iota. step.
    eapply tail; [exact Efv | hfc | eassumption | exact FM7 |].
    unfold pn_bin; rewrite FE, LT, LE. unfold pn_r. cbv zeta. rewrite GE. reflexivity. }
  (* E+0xe8 a0:a1 = frac, a2:a3 = -0.5L; jal __cmptf2 *)
  do 6 step.
  eapply evt_cut.
  { eapply (br_le NI.N_img rsegs NI.B_CMPTF2 eq_refl eq_refl HLE);
      [exact (frm_mi _ _ FM7) | exact (tm_frm _ _ FM7)]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & -> & MU8 & WM8 & MI8 & _).
  pose proof (frm_call _ _ _ FM7 MU8 WM8 MI8) as FM8. clear FM7 MU8 WM8 MI8.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 MHALF_128.
  (* E+0x100 bgez a0 *)
  step. rewrite lts0 by apply f128_le_range.
  destruct (SF.f128_le (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) MHALF_128 <? 0) eqn:LM;
    cbn [negb]; cbv iota.
  - (* frac < -1/2: E+0x104 addi a0,s1,-1; blt a0,s1 -> E+0x118 (taken: t - 1 does not overflow); mv s1,a0;
       r = t - 1 *)
    step. step. rewrite (lts_dec (pn_t b) T3). cbv iota. step.
    eapply tail; [exact Efv | hfc | eassumption | exact FM8 |].
    unfold pn_bin; rewrite FE, LT, LE. unfold pn_r. cbv zeta. rewrite GE, LM.
    replace (pn_t b - 1) with (pn_t b + -1) by lia. reflexivity.
  - (* r = t *)
    eapply tail; [exact Efv | hfc | eassumption | exact FM8 |].
    unfold pn_bin; rewrite FE, LT, LE. unfold pn_r. cbv zeta. rewrite GE, LM. reflexivity.
Qed.

End Walk.

(** The contract of image B's pod_nearest, from the binary128 value facts [near_sf_facts] and the contracts of the
    five soft-float callees at image B's symbol map (lib/AU/RtPgNearImgB.v N_img). *)
Theorem pod_nearest_B_holds :
  pod_nearest.near_sf_facts ->
  @C_extendsftf2.extendsftf2_contract NI.N_img -> @G_letf2.letf2_contract NI.N_img ->
  @C_floatditf.floatditf_contract NI.N_img -> @G_subtf3.subtf3_contract NI.N_img ->
  @G_getf2.getf2_contract NI.N_img ->
  RtPgNearCB.pod_nearest_B_contract.
Proof.
  intros NS HEX HLE HFD HSB HGE. pose proof (pn_bin_nearest NS) as HV. unfold pod_nearest_B_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b
    Hb HF WR Hal Hdj ST HK HW HLO HGOT HCELL HSH HSHo FRM MI TM.
  replace (nearest b INT32_MIN INT32_MAX) with (pn_bin b) by (rewrite (HV b Hb); reflexivity).
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  set (Sp := bv_unsigned sp) in *. set (out := bv_unsigned a0) in *.
  rewrite <- Esp, <- Ea0. clearbody Sp out. clear Esp Ea0.
  unfold B_NEAR_STACK, B_SHADOW_OFF in *.
  pose proof ST as (Hlo & HSp & STw).
  assert (Hout : 0 <= out /\ out + 8 <= 2^64) by (destruct WR as (W1 & W2 & _); split; assumption).
  assert (Hdj' : hold (out + 8 <= Sp - 112 \/ Sp <= out)) by exact Hdj.
  assert (HGOT' : hold (bytes_at rsegs m NI.B_GOT_SHADOW (le8 (Z_to_bv 64 NI.B_SHADOW_CELL)))) by exact HGOT.
  assert (HCELL' : hold (bytes_at rsegs m NI.B_SHADOW_CELL (le8 (Z_to_bv 64 0x7fff8000)))) by exact HCELL.
  assert (HSH' : hold (bytes_at rsegs m (0x7fff8000 + out / 8) [Z_to_bv 8 0])) by exact HSH.
  assert (HSHo' : hold (outside [(Sp - 112, Sp)] (0x7fff8000 + out / 8))) by exact HSHo.
  assert (WR0 : forall x : word, Sp - 112 <= bv_unsigned x < Sp \/ out <= bv_unsigned x < out + 8 ->
                  wview rsegs m x <> None).
  { intros x [Hx|Hx].
    - rewrite <- (Z_to_bv_lit_self x). exact (proj1 (STw (bv_unsigned x) ltac:(lia))).
    - destruct WR as (_ & _ & W3). specialize (W3 (bv_unsigned x - out) ltac:(lia)).
      replace (out + (bv_unsigned x - out)) with (bv_unsigned x) in W3 by lia.
      unfold wa in W3. rewrite Z_to_bv_lit_self in W3. exact W3. }
  clear Hdj HGOT HCELL HSH HSHo.
  eapply evt_mono.
  { eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m b Sp out lo); eassumption. }
  intros ms' H. exact H.
Qed.

Print Assumptions pod_nearest_B_holds.
