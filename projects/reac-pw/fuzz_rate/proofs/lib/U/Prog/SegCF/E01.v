(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 269 of its 301 lines of code are new or changed and 543 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/E01.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_role's U/Prog/SegCF/E01.v, as libreac/fuzz_ctrl's released
   U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg -> SegCF, the
   segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the allocator
   contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Segment E01 of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (UBSan): [0x12fe0, 0x1310c] with the out-of-line header
   reads [0x143d0, 0x1446c], ENTRY -> K13110 (U/Prog/LLVMFuzzerTestOneInput_c.v's S_E01).
   reac-pw/fuzz_role's U/Prog/Seg/E01.v with rate's UBSan numbers and
   rate's seven-byte header (fuzz_rate.c:233-240, fuzz.h:37-56):
   - the prologue (0x12fe0 `addi sp,sp,-0x250`; ra, s0 .. s11 saved at S - 8 .. S - 104), the n >= 2^26 exit not
     taken (0x13018 `srli a2,a1,26`, 0x1301c `beqz a2`: GV bounds n below 2^26), 0x13024 `mv s7,a0`;
   - the header, one path for each n = 0, 1, .., 6 and one for n >= 7: fuzz_u8 reads byte i when one is left, else
     the value is 0 and no later byte is read. Each read first checks the pointer data + i + 1 (0x13034, 0x13050,
     0x130ac `bltu 1,a2`; 0x143d8, 0x14400, 0x1442c, 0x14454 `bgeu 1,a2`; the other side traps at 0x146bc `unimp`):
     dead, as the input block starts above 0 and ends below the stack window, so data + i + 1 neither wraps nor is
     below 2. The values: s2 = byte 0 (0x1303c), s5 = byte 1 (0x13058), the cell sp + 0x30 = byte 2 mod 24
     (0x130b4-0x130dc: `ld` of the constant 0x0aaaaaaaaaaaaaab at .rodata 0x104e0 through auipc, `mulhu`, `slli 5`,
     `slli 3`, `sub`, `add`), s4 = byte 3 (0x143dc), the cell sp + 0x28 = byte 4 << 8 (0x14414), the cell sp + 0x20 =
     byte 5 (0x1443c), the cell sp + 0x18 = byte 6 << 8 (0x14468), each 0 when absent (the `sd zero` stores at
     0x13068 .. 0x130f8, 0x143f0), s1 = n - 7 or 0, s7 = data + min 7 n (0x14460 or 0x130fc `mv s7,a2`); the bytes 3..6
     lie out of line (0x130e4 `j 0x143d0`, back by 0x143f4 / 0x14420 -> 0x130f4, 0x14448 -> 0x130f8, 0x1446c ->
     0x13100);
   - 0x13100 `lui s0,5`, `addiw s3,s0,-0x2e0` (19744), `mv a0,s3`, and malloc(19744) at 0x1310c with ra = 0x13110
     through Tac_b1.b1_malloc_call from hb = [], whose continuation gives Inv_K13110. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

(* ---- The quantities of the header (SlotInv's g_u8, g_k, g_src for inp = g_in g, p = g_p g) ---- *)
Definition e01_u8 (inp : list byte) (i : nat) : Z :=
  match nth_error inp i with Some b => bv_unsigned b | None => 0 end.
Definition e01_k (inp : list byte) : Z := Z.of_nat (length inp) - Z.min 7 (Z.of_nat (length inp)).
Definition e01_src (p : Z) (inp : list byte) : Z := p + Z.min 7 (Z.of_nat (length inp)).

Lemma e01_rd0 : forall m (a : word) b l, bytes_at rsegs m (bv_unsigned a) (b :: l) ->
  ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m a b l H.
  assert (E : a = wa (bv_unsigned a + Z.of_nat 0)).
  { unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. }
  rewrite E. rewrite (bytes_at_ov_read rsegs m (bv_unsigned a) (b :: l) 0 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma e01_firstn1 : forall (l : list byte) j b, nth_error l j = Some b -> firstn 1 (skipn j l) = [b].
Proof.
  induction l as [|x l IH]; intros [|j] b E; cbn in *; try discriminate.
  - inversion E. reflexivity.
  - apply IH. exact E.
Qed.

(* Byte k of the input, for the input list l = l' (the destructed one). *)
Lemma e01_rdz : forall m (p : Z) (l l' : list byte) (k : Z) b, bytes_at rsegs m p l -> l = l' -> 0 <= k ->
  nth_error l' (Z.to_nat k) = Some b -> ov_read_bytes rsegs m (wa (p + k)) 1 = Some [b].
Proof.
  intros m p l l' k b H <- Hk E.
  assert (Hlt : (Z.to_nat k < length l)%nat) by (apply nth_error_Some; congruence).
  replace (p + k) with (p + Z.of_nat (Z.to_nat k)) by (rewrite Z2Nat.id by lia; reflexivity).
  rewrite (bytes_at_ov_read rsegs m p l (Z.to_nat k) 1 H) by lia.
  rewrite (e01_firstn1 l (Z.to_nat k) b E). reflexivity.
Qed.

Lemma e01_weq_l : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

(* 0x13018 `srli a2,a1,26`; 0x1301c `beqz a2`: taken for n < 2^26. *)
Lemma e01_cond : forall u, 0 <= u < 2 ^ 26 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = true.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

(* The byte ranges of the destructed input, once each. *)
Ltac e01_rng :=
  repeat match goal with
  | b : byte |- _ =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned b < 256 |- _ => fail
      | _ => pose proof (b1_byte_rng b)
      end
  end.

Ltac e01_weq :=
  first [ reflexivity
        | apply e01_weq_l; unfold zxb; fold_lit_ux; rewrite ?unsigned_lit_wrap;
          rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
          Z.div_mod_to_equations; lia ].

(* A branch: keep the side the facts allow (the trap sides of the pointer checks are refuted from 0 < p and
   p + n below the stack window; the length tests from n). *)
Ltac e01_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "EC" in if_cases H; zify_cond H; try (exfalso; lia)
  end.

(* Before the read of byte k (lbu at the pcs below): its ov_read_bytes in the current memory. Byte 0 is read at
   the cursor word itself (0x1303c `lbu s2,0(s7)` with s7 = a0), the others at data + k. *)
Ltac e01_rd k :=
  lazymatch goal with
  | Hb : bytes_at rsegs ?m ?p ?l, El : ?l = _ |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      let HR := fresh "HR" in
      lazymatch k with
      | 0 =>
          lazymatch p with bv_unsigned ?w =>
            lazymatch type of El with _ = ?b :: ?l' =>
              pose proof (e01_rd0 m w b l' ltac:(rewrite <- El; exact Hb)) as HR
            end
          end
      | _ => pose proof (e01_rdz m p l _ k _ Hb El ltac:(lia) eq_refl) as HR
      end
  end.

Ltac e01_pre pc :=
  lazymatch pc with
  | 0x1303c => e01_rd constr:(0)
  | 0x13058 => e01_rd constr:(1)
  | 0x130b4 => e01_rd constr:(2)
  | 0x143dc => e01_rd constr:(3)
  | 0x14404 => e01_rd constr:(4)
  | 0x14430 => e01_rd constr:(5)
  | 0x14458 => e01_rd constr:(6)
  | _ => idtac
  end.

(* Run to malloc's entry 0x16a7c. *)
Ltac e01_run :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x16a7c) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => e01_pre pc; step
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => e01_if
  end.

(* ---- The run: ENTRY to malloc's entry with ra = 0x13110 ---- *)
Definition e01_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p : Z) (inp : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s7' t3' t4' t5' t6'
          c18 c20 c28 c30 : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x13110) (Z_to_bv 64 (bv_unsigned sp + -592)) gp tp t0' t1' t2' s0' s1' a0' a1' a2'
                  a3' a4' a5' a6' a7' s2' s3' s4' s5' s6 s7' s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x16a7c) fc None m' (seg_rom rsegs) /\
    Frame.munch [(bv_unsigned sp - 592, bv_unsigned sp)] m m' /\ Frame.wmono rsegs m m' /\
    bytes_at rsegs m' (bv_unsigned sp - 568) (le8 c18 ++ le8 c20 ++ le8 c28 ++ le8 c30) /\
    bytes_at rsegs m' (bv_unsigned sp - 104)
      (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
       le8 s1 ++ le8 s0 ++ le8 ra) /\
    s0' = Z_to_bv 64 0x5000 /\ s3' = Z_to_bv 64 POD_PROPS /\ a0' = Z_to_bv 64 POD_PROPS /\
    s7' = Z_to_bv 64 (e01_src p inp) /\ s1' = Z_to_bv 64 (e01_k inp) /\
    s2' = Z_to_bv 64 (e01_u8 inp 0) /\ s5' = Z_to_bv 64 (e01_u8 inp 1) /\ s4' = Z_to_bv 64 (e01_u8 inp 3) /\
    c18 = Z_to_bv 64 (e01_u8 inp 6 * 256) /\ c20 = Z_to_bv 64 (e01_u8 inp 5) /\
    c28 = Z_to_bv 64 (e01_u8 inp 4 * 256) /\ c30 = Z_to_bv 64 (e01_u8 inp 2 mod 24).

(* The frame is carved in two: the thirteen saved registers at S - 104 (FRS) and, below them, the four eight-byte
   header cells at S - 568 .. S - 536 with the gap above them (FRC). *)
Ltac e01_fin sp FRS FRC :=
  let SB := fresh "SB" in let SF := fresh "SF" in
  pose proof (sl_cells_bytes _ _ _ FRS) as SB;
  pose proof (sl_cells_bytes _ _ _ FRC) as SF;
  cbn [Cells.cells_bytes Cells.cbytes] in SB, SF; rewrite ?app_nil_r in SB, SF;
  rewrite !app_assoc in SF; apply bytes_at_app in SF; destruct SF as [SF _]; rewrite <- !app_assoc in SF;
  lazymatch type of SB with bytes_at _ _ ?x _ => replace x with (bv_unsigned sp - 104) in SB by lia end;
  lazymatch type of SF with bytes_at _ _ ?y _ => replace y with (bv_unsigned sp - 568) in SF by lia end;
  apply evt_done; unfold e01_post;
  do 27 eexists; split; [reflexivity|];
  split; [assumption|]; split; [assumption|]; split; [exact SF|]; split; [exact SB|];
  repeat match goal with |- _ /\ _ => split end.

Ltac e01_eqs := unfold e01_k, e01_src, e01_u8, POD_PROPS; cbn [length nth_error]; e01_rng; e01_weq.

Lemma e01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (inp : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 592 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a0 = p -> bv_unsigned a1 = Z.of_nat (length inp) -> Z.of_nat (length inp) < 2 ^ 26 ->
    0 < p -> p + Z.of_nat (length inp) <= lo -> bytes_at rsegs m p inp ->
    evt rsegs (e01_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p inp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fe0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p inp ST LO HMI0 Ep Ha1 H26 Hp0 Hin Hb.
  subst p.
  (* The input list of Hb and Hin stays a variable l (the stores' disjointness side conditions see length l);
     the case split below is on inp, with El : l = inp. *)
  remember inp as l eqn:El in Hb, Hin.
  assert (Hll : Z.of_nat (length l) = bv_unsigned a1) by (rewrite El; lia).
  pose proof (munch_refl [(bv_unsigned sp - 592, bv_unsigned sp)] m) as MU.
  assert (Hlo : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 104%nat ST.
  rename FR into FRS.
  carve_frame 464%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 464%nat _ [] [8%nat; 8%nat; 8%nat; 8%nat; 432%nat]) in FR; [|reflexivity].
  cbn [app mk_CB_cells] in FR.
  rename FR into FRC.
  do 16 step.
  if_true_by (e01_cond (bv_unsigned a1) ltac:(lia)).
  step.
  destruct inp as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 rest]]]]]]]; cbn [length] in Ha1, H26;
    e01_run; e01_fin sp FRS FRC; e01_eqs.
Qed.

(* ---- The segment ---- *)
Ltac e01_rp RP Hx r :=
  etransitivity; [exact (RP r ltac:(unfold callee_saved; lia))|]; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.

Lemma e01_addr : forall m a a' bs, bytes_at rsegs m a bs -> a = a' -> bytes_at rsegs m a' bs.
Proof. intros m a a' bs H <-. exact H. Qed.

(* The four header cells at S - 568 .. S - 536, one by one. *)
Lemma e01_cells4 : forall m a v1 v2 v3 v4, bytes_at rsegs m a (le8 v1 ++ le8 v2 ++ le8 v3 ++ le8 v4) ->
  bytes_at rsegs m a (le8 v1) /\ bytes_at rsegs m (a + 8) (le8 v2) /\ bytes_at rsegs m (a + 16) (le8 v3) /\
  bytes_at rsegs m (a + 24) (le8 v4).
Proof.
  intros m a v1 v2 v3 v4 H.
  apply bytes_at_app in H. destruct H as [H1 H]. rewrite length_le8 in H.
  apply bytes_at_app in H. destruct H as [H2 H]. rewrite length_le8 in H.
  apply bytes_at_app in H. destruct H as [H3 H4]. rewrite length_le8 in H4.
  split; [exact H1|].
  split; [apply (e01_addr _ _ _ _ H2); lia|].
  split; [apply (e01_addr _ _ _ _ H3); lia | apply (e01_addr _ _ _ _ H4); lia].
Qed.

Section E01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.

Lemma seg_E01 : S_E01 B APIf ra empty.
Proof.
  unfold S_E01. intros H1 g c (Ec & HGV & Hpre & Hsp & Hsn & HMI & Hrel & Hres & Hfrm).
  subst c.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSK & HS47 & _ & HGsp & HGtp).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  pose proof sl_ceil as Hct.
  pose proof (ff_empty B APIf ra empty FF) as Hemp.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Esp2 : bv_unsigned (YK11.getr (g_regs g) 2) = g_S g).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  (* The input block lies below alloc_ceiling, so below the stack window; its address is positive
     (an input block starts at 4096 or above; for the empty input the cursor is the `empty` global). *)
  assert (Hpb : 0 < g_p g /\ g_p g + g_n g <= g_S g - 65536).
  { destruct Hpl as [(Hn0 & Hpe) | (Hn0 & Hin)].
    - rewrite Hn0, Hpe, (ff_empty_val B APIf ra empty FF). lia.
    - destruct (b1_blk B APIf ra empty FF _ _ _ _ _ _ HM Hin) as (_ & Hb1 & Hb2). lia. }
  assert (Ep : bv_unsigned (YK11.getr (g_regs g) 10) = g_p g).
  { rewrite Hp. apply MState.unsigned_lit. lia. }
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = Z.of_nat (length (g_in g))).
  { rewrite Hn. apply MState.unsigned_lit. unfold g_n in *. lia. }
  unfold MI in HMI. rewrite SEGS in HMI.
  assert (Hdat' : bytes_at rsegs (normalize rsegs (g_mem g)) (g_p g) (g_in g)).
  { apply (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs (g_mem g) HMI))).
    split; [lia|]. split; [unfold g_n in Hpb; lia|].
    intros k Hk. pose proof (Hdat (Z.of_nat k) ltac:(lia)) as E. rewrite Nat2Z.id, SEGS in E. exact E. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. unfold ENTRY.
    apply e01_evt with (lo := g_S g - 65536) (p := g_p g) (inp := g_in g).
    + rewrite Esp2. apply sl_stk_norm; [exact HMI | unfold SL_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + rewrite Esp2. lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + exact Ep.
    + exact En.
    + unfold g_n in Hn26. lia.
    + lia.
    + unfold g_n in Hpb. lia.
    + exact Hdat'.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?
               & m'' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' &
                    s5' & s7' & t3' & t4' & t5' & t6' & c18 & c20 & c28 & c30 & m'' & HE & MU & WM & SF & SB &
                    E8 & E19 & E10 & E23 & E9 & E18 & E21 & E20 & C18 & C20 & C28 & C30).
    injection HE; intros; subst.
    rewrite Esp2 in MU, SB, SF.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 592, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' _ HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' _ HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    pose proof (proj2 (bytes_at_rel rsegs m' _ _ _ Hrel') SB) as SB'.
    pose proof (proj2 (bytes_at_rel rsegs m' _ _ _ Hrel') SF) as SF'.
    destruct (e01_cells4 _ _ _ _ _ _ SF') as (K18 & K20 & K28 & K30).
    pose proof (e01_addr _ _ (fsp g + 0x18) _ K18 ltac:(unfold fsp, SLOT_FRAME; lia)) as C18'.
    pose proof (e01_addr _ _ (fsp g + 0x20) _ K20 ltac:(unfold fsp, SLOT_FRAME; lia)) as C20'.
    pose proof (e01_addr _ _ (fsp g + 0x28) _ K28 ltac:(unfold fsp, SLOT_FRAME; lia)) as C28'.
    pose proof (e01_addr _ _ (fsp g + 0x30) _ K30 ltac:(unfold fsp, SLOT_FRAME; lia)) as C30'.
    clear K18 K20 K28 K30.
    assert (HFR : FR B APIf ra empty g [] (g_L g) (g_A g) regs' m' (g_md g)).
    { apply (sl_fr_of B APIf ra empty FF) with (mem0 := g_mem g).
      - exact HGV.
      - exact HM.
      - exact HW.
      - exact HB.
      - exact HID.
      - exists (m_vmmaps (g_md g)). apply with_vmmaps_self.
      - intros a _ _ _. split; [reflexivity | tauto].
      - intros a _ _ _ _. split; [reflexivity | tauto].
      - intros a k i _ _. reflexivity.
      - intros a k Hin. exact Hin.
      - exact Herr.
      - exact Hsn.
      - exact (resb_start (g_b g) (g_A g) Hres).
      - intros a Ha. apply Hstw. rewrite Esp. unfold SLOT_K, SLOT_STACK in Ha. exact Ha.
      - exact Hrel.
      - apply (sl_unch _ _ _ (g_S g - 65536) (g_S g) MU').
        intros x Hx0 O. destruct (Z_le_dec (g_S g - 592) x); destruct (Z_lt_dec x (g_S g)); try lia;
          exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr (g_regs g) 2) + -592)); [reflexivity|].
        rewrite Esp2. unfold fsp, SLOT_FRAME. f_equal; lia.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - unfold saved_bytes, SLOT_SAVE. rewrite <- Hra. exact SB'. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x13110) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 POD_PROPS) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g [] (g_L g) (g_A g) regs' m' (g_md g) regs' POD_PROPS);
      [exact HFR | cbn [app]; apply Permutation_refl | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity
      | rewrite E1; vm_compute; reflexivity | exact E10' | unfold POD_PROPS; lia |].
    intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 Hres16 HK HKH.
    assert (CELL : forall a bs, bytes_at rsegs m' a bs -> fsp g <= a -> a + Z.of_nat (length bs) <= g_S g ->
                     bytes_at rsegs mem'' a bs).
    { intros a bs Hab H1a H2a. apply (b1_ba_mbyte m'); [exact Hab|].
      intros i Hi. apply HK. lia. }
    rewrite E1. apply H1. exists res, fx, L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF''|]. split; [exact HP''|].
    unfold rg. split; [exact Hres10|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [e01_rp RP Hx 23|]. split; [e01_rp RP Hx 9|]. split; [e01_rp RP Hx 18|]. split; [e01_rp RP Hx 21|].
    split; [apply CELL; [exact C30' | unfold fsp, SLOT_FRAME; lia | rewrite length_le8; unfold fsp, SLOT_FRAME; lia]|].
    split; [e01_rp RP Hx 20|].
    split; [apply CELL; [exact C28' | unfold fsp, SLOT_FRAME; lia | rewrite length_le8; unfold fsp, SLOT_FRAME; lia]|].
    split; [apply CELL; [exact C20' | unfold fsp, SLOT_FRAME; lia | rewrite length_le8; unfold fsp, SLOT_FRAME; lia]|].
    split; [apply CELL; [exact C18' | unfold fsp, SLOT_FRAME; lia | rewrite length_le8; unfold fsp, SLOT_FRAME; lia]|].
    split; [e01_rp RP Hx 19|]. e01_rp RP Hx 8.
Qed.

End E01.
