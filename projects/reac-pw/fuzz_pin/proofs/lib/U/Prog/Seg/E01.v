(* Segment E01 of reac-pw/fuzz_pin LLVMFuzzerTestOneInput (UBSan): [0x12cbc, 0x12d4c], ENTRY -> K12d50.
   The plain segment (lib/Prog/Seg/E01.v) with the UBSan numbers and the three UBSan checks of this stretch:
   the prologue (0x12cbc `addi sp,sp,-80`; ra, s0-s5 saved at S - 8 .. S - 56), the n >= 2^26 exit not taken (GV),
   s1 = data, then n = 0 (0x12d08: s2 = 0, s3 = 0, s0 = data) or n >= 1 (0x12cec s0 = data + 1, the check
   0x12cf4 `bgeu a0,s0`, 0x12cf8 `lbu s3,0(s1)` = the flags, s2 = n - 1, s1 = s0); both join at 0x12d14, where
   0x12d18 `bltu a0,s0` and 0x12d28 `beqz a0` (the pointer-overflow check) are the other two UBSan traps; they are
   refuted from 0 < data and data + n <= alloc_ceiling. 0x12d2c skips memchr when n <= 1 (through 0x12e54), else
   memchr(data + 1, 0, n - 1) at 0x12d3c (U/Prog/memchr_c.v, MEMCHR = 0x1ab44) and 0x12d44 `sub s2,a0,s0`;
   k = the NUL's index or n - 1 or 0, and malloc(k + 1) at 0x12d4c with ra = 0x12d50 through U Tac_b1's
   b1_malloc_call, whose continuation gives Inv_K12d50 (k in s2, the rest in s1: the UBSan build swaps them
   against the plain one).
   Adapted from libreac/fuzz_ctrl's released segments A01 (the run from Inv_ENTRY on the normalized memory, FR with
   hb = []) and F01 (malloc as a Kind B step) (origin/ossv/recipes 25e3d17bdb50, Prog/Seg/); memchr is called inside
   the run by evt_cut over memchr_c.memchr_contract, as reac-pw/fuzz_qdisc's walk calls its leaves. The bridge
   lemmas e01_find_nul_some / e01_find_nul_none give memchr's result as pin_spec.pin_k. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import SlotInv memchr_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

(* ---- memchr's result is the first NUL of the rest (pin_spec.nul_idx) ---- *)
Lemma e01_find_nul_some : forall l i, find_byte 0 l = Some i -> nul_idx l = i.
Proof.
  induction l as [|b l IH]; intros i H; cbn [find_byte] in H; [discriminate|].
  cbn [nul_idx]. destruct (bv_unsigned b =? 0).
  - injection H as <-. reflexivity.
  - destruct (find_byte 0 l) as [j|] eqn:E; [|discriminate]. injection H as <-. f_equal. apply IH. reflexivity.
Qed.

Lemma e01_find_nul_none : forall l, find_byte 0 l = None -> nul_idx l = length l.
Proof.
  induction l as [|b l IH]; intros H; cbn [find_byte] in H; [reflexivity|].
  cbn [nul_idx length]. destruct (bv_unsigned b =? 0); [discriminate|].
  destruct (find_byte 0 l) as [j|] eqn:E; [discriminate|]. f_equal. apply IH. reflexivity.
Qed.

Lemma e01_mres_some : forall A c n buf A' i, find_byte 0 buf = Some i ->
  n = Z.of_nat (length buf) -> c = 0 -> A = A' -> memchr_res A c n buf = A' + Z.of_nat i.
Proof.
  intros A c n buf A' i EF -> -> ->. unfold memchr_res. rewrite Nat2Z.id, firstn_all, EF. reflexivity.
Qed.

Lemma e01_mres_none : forall A c n buf, find_byte 0 buf = None ->
  n = Z.of_nat (length buf) -> c = 0 -> memchr_res A c n buf = 0.
Proof.
  intros A c n buf EF -> ->. unfold memchr_res. rewrite Nat2Z.id, firstn_all, EF. reflexivity.
Qed.

(* memchr reads exactly the n - 1 bytes of the rest, so its premise holds. *)
Lemma e01_mok : forall A c n buf, n = Z.of_nat (length buf) -> memchr_ok A c n buf.
Proof.
  intros A c n buf ->. unfold memchr_ok. rewrite Nat2Z.id, firstn_all.
  destruct (find_byte c buf); [left|]; lia.
Qed.

Lemma e01_k_le : forall inp, (pin_k inp <= length inp)%nat.
Proof.
  intros inp. unfold pin_k, pin_rest. pose proof (nul_idx_le (tl inp)).
  destruct inp; cbn [tl length] in *; lia.
Qed.

Lemma e01_k_nil : pin_k [] = 0%nat.
Proof. reflexivity. Qed.

Lemma e01_k_cons : forall b l, pin_k (b :: l) = nul_idx l.
Proof. reflexivity. Qed.

Lemma e01_fl_nil : pin_flags [] = 0.
Proof. reflexivity. Qed.

Lemma e01_fl_cons : forall b l, pin_flags (b :: l) = bv_unsigned b.
Proof. reflexivity. Qed.

(* ---- Bytes and words ---- *)
Lemma e01_rd0 : forall m (a : word) b l, bytes_at rsegs m (bv_unsigned a) (b :: l) ->
  ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m a b l H.
  assert (E : a = wa (bv_unsigned a + Z.of_nat 0)).
  { unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. }
  rewrite E. rewrite (bytes_at_ov_read rsegs m (bv_unsigned a) (b :: l) 0 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma e01_ba_tl : forall m a b l, bytes_at rsegs m a (b :: l) -> bytes_at rsegs m (a + 1) l.
Proof.
  intros m a b l (H1 & H2 & H). cbn [length] in H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply H. cbn [length]. lia.
Qed.

Lemma e01_ba_eq : forall m a' a bs, bytes_at rsegs m a bs -> a = a' -> bytes_at rsegs m a' bs.
Proof. intros m a' a bs H ->. exact H. Qed.

Lemma e01_weq_l : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

(* 0x12cdc `srli a2,a1,26`; 0x12ce0 `bnez a2`: not taken for n < 2^26 (ctrl's a01_cond). *)
Lemma e01_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

Ltac e01_weq :=
  first [ reflexivity
        | apply e01_weq_l; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Ltac e01_side :=
  cbn [length];
  first [ reflexivity | zsimp; lia | rewrite ?MState.unsigned_lit by lia; lia | vm_compute; reflexivity ].

(* 0x12d28 `beqz a0`: the pointer-overflow trap. a0 is `snez s1 xor seqz (s1 + k0)`, which is 1 when the rest is
   non-NULL and its end does not wrap, so the branch to the trap site is not taken. *)
Lemma e01_ptr_ok : forall x y, 0 < x -> 0 < y ->
  Z.lxor (Z.b2z (0 <? x)) (Z.b2z (y <? 1)) = 0 -> False.
Proof.
  intros x y Hx Hy H.
  rewrite (proj2 (Z.ltb_lt 0 x)) in H by lia.
  rewrite (proj2 (Z.ltb_ge y 1)) in H by lia.
  cbn in H. discriminate H.
Qed.

(* A dead branch whose condition mentions the UBSan pointer test (snez / seqz / xor). *)
Ltac e01_kill H :=
  exfalso;
  first [ refine (e01_ptr_ok _ _ _ _ H); lia
        | (repeat match type of H with
           | context [Z.ltb ?x ?y] =>
               first [ rewrite (proj2 (Z.ltb_lt x y)) in H by lia
                     | rewrite (proj2 (Z.ltb_ge x y)) in H by lia ]
           end);
          cbn in H; first [ lia | discriminate H | exact H ] ].

(* A branch: keep the side the facts allow. *)
Ltac e01_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "EC" in if_cases H; zify_cond H; try (exfalso; lia); try (e01_kill H)
  | _ => idtac
  end.

(* ---- The run: ENTRY to malloc's entry with ra = 0x12d50 ---- *)
Definition e01_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p : Z) (inp : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x12d50) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0' s1' a0' a1' a2'
                  a3' a4' a5' a6' a7' s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x13d04) fc None m' (seg_rom rsegs) /\
    s0' = Z_to_bv 64 (p + Z.min 1 (Z.of_nat (length inp))) /\
    s1' = Z_to_bv 64 (p + Z.min 1 (Z.of_nat (length inp))) /\
    a0' = Z_to_bv 64 (Z.of_nat (pin_k inp) + 1) /\
    s2' = Z_to_bv 64 (Z.of_nat (pin_k inp)) /\ s3' = Z_to_bv 64 (pin_flags inp) /\
    Frame.munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ Frame.wmono rsegs m m' /\
    bytes_at rsegs m' (bv_unsigned sp - 56)
      (le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra).

Ltac e01_fin sp :=
  lazymatch goal with
  | FR : rw_cells _ _ _ (CB _ _ :: _) |- _ =>
      let SB := fresh "SB" in
      pose proof (sl_bytes_cells_tail _ _ _ _ _ FR) as SB;
      cbn [Cells.cells_bytes Cells.cbytes] in SB; rewrite ?app_nil_r in SB;
      lazymatch type of SB with bytes_at _ _ ?x _ => replace x with (bv_unsigned sp - 56) in SB by lia end;
      apply evt_done; unfold e01_post;
      do 20 eexists; split; [reflexivity|];
      split; [|split; [|split; [|split; [|split; [|split; [assumption|split; [assumption|exact SB]]]]]]]
  end.

Ltac e01_eqs :=
  rewrite ?e01_k_nil, ?e01_k_cons, ?e01_fl_nil, ?e01_fl_cons;
  try match goal with
      | EF : find_byte 0 ?l = Some _ |- context [nul_idx ?l] => rewrite (e01_find_nul_some _ _ EF)
      | EF : find_byte 0 ?l = None |- context [nul_idx ?l] => rewrite (e01_find_nul_none _ EF)
      end;
  cbn [nul_idx length]; e01_weq.

Lemma e01_evt : memchr_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (inp : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a0 = p -> bv_unsigned a1 = Z.of_nat (length inp) -> Z.of_nat (length inp) < 2 ^ 26 ->
    0 < p -> p + Z.of_nat (length inp) <= lo -> bytes_at rsegs m p inp ->
    evt rsegs (e01_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p inp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12cbc) fc None m (seg_rom rsegs)).
Proof.
  intros MCHR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p inp ST LO HMI0 Ep Ha1 H26 Hp0 Hin Hb.
  unfold memchr_contract in MCHR.
  subst p.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  assert (Hlo : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 80%nat ST.
  do 10 step.
  if_false_by (e01_cond (bv_unsigned a1) ltac:(lia)).
  step. step.
  destruct inp as [|b0 [|b1 rest]]; cbn [length] in Ha1, H26, Hin.
  - (* n = 0: s2 = 0, s3 = 0, s0 = data *)
    e01_if.
    do 5 step. e01_if.
    do 4 step. e01_if.
    step. e01_if.
    step. step. e01_if.
    do 3 step.
    e01_fin sp.
    all: e01_eqs.
  - (* n = 1: fl = data[0], k = 0 *)
    e01_if.
    pose proof (e01_rd0 _ _ _ _ Hb) as HB0.
    do 3 step. e01_if.
    do 4 step.
    step. step. e01_if.
    do 4 step. e01_if.
    step. e01_if.
    step. step. e01_if.
    do 3 step.
    e01_fin sp.
    all: e01_eqs.
  - (* n >= 2: memchr(data + 1, 0, n - 1) *)
    e01_if.
    pose proof (e01_rd0 _ _ _ _ Hb) as HB0.
    pose proof (e01_ba_tl _ _ _ _ Hb) as HB1.
    do 3 step. e01_if.
    do 4 step.
    step. step. e01_if.
    do 4 step. e01_if.
    step. e01_if.
    do 4 step.
    lazymatch goal with
    | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply MCHR with (buf := b1 :: rest);
          [ eapply e01_ba_eq; [exact HB1 | e01_side] | apply e01_mok; e01_side | assumption ]
        | post_call segs mm ]
    end.
    destruct (find_byte 0 (b1 :: rest)) as [i|] eqn:EF.
    + pose proof (find_byte_Some _ _ _ EF) as (Hi & _ & _). cbn [length] in Hi.
      lazymatch goal with
      | |- context [memchr_res ?A ?c ?n ?buf] =>
          rewrite (e01_mres_some A c n buf (bv_unsigned a0 + 1) i EF) by e01_side
      end.
      step. e01_if. step. step. step.
      e01_fin sp.
      all: e01_eqs.
    + lazymatch goal with
      | |- context [memchr_res ?A ?c ?n ?buf] =>
          rewrite (e01_mres_none A c n buf EF) by e01_side
      end.
      step. e01_if. step. step.
      e01_fin sp.
      all: e01_eqs.
Qed.

(* ---- The segment ---- *)
Ltac e01_rp RP Hx r :=
  etransitivity; [exact (RP r ltac:(unfold callee_saved; lia))|]; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.

Section E01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Hypothesis MCHR : memchr_c.memchr_contract.

Lemma seg_E01 : S_E01 B APIf ra empty.
Proof.
  unfold S_E01. intros H1 g c (Ec & HGV & Hpre & Hsp & Hsn & HMI & Hrel & Hres).
  subst c.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSK & HS47 & _ & HGsp & HGtp).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  pose proof sl_ceil as Hct.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Esp2 : bv_unsigned (YK11.getr (g_regs g) 2) = g_S g).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  (* The input block lies below alloc_ceiling, so below the stack window; and its address is positive. *)
  assert (Hpb : 0 < g_p g /\ g_p g + g_n g <= g_S g - 65536).
  { destruct Hpl as [(Hn0 & Hpe) | (Hn0 & Hinb)].
    - rewrite Hn0, Hpe, (ff_empty_val B APIf ra empty FF). lia.
    - destruct (b1_blk B APIf ra empty FF _ _ _ _ _ _ HM Hinb) as (_ & Hb1 & Hb2). lia. }
  assert (Ep : bv_unsigned (YK11.getr (g_regs g) 10) = g_p g).
  { rewrite Hp. apply MState.unsigned_lit. lia. }
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = Z.of_nat (length (g_in g))).
  { rewrite Hn. apply MState.unsigned_lit. unfold g_n in *. lia. }
  unfold MI in HMI. rewrite SEGS in HMI.
  assert (Hdat' : bytes_at rsegs (normalize rsegs (g_mem g)) (g_p g) (g_in g)).
  { apply (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs (g_mem g) HMI))).
    split; [lia|]. split; [unfold g_n in Hpb; lia|].
    intros k Hk. pose proof (Hdat (Z.of_nat k) ltac:(lia)) as E. rewrite Nat2Z.id, SEGS in E. exact E. }
  assert (Hk : 0 <= g_k g + 1 <= 2 ^ 26).
  { pose proof (e01_k_le (g_in g)). unfold g_k. unfold g_n in Hn26. lia. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. unfold ENTRY.
    apply (e01_evt MCHR) with (lo := g_S g - 65536) (p := g_p g) (inp := g_in g).
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
  - intros ms (t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & t3' & t4' &
               t5' & t6' & m'' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & t3' &
                    t4' & t5' & t6' & m'' & HE & E8 & E9 & E10 & E18 & E19 & MU & WM & SB).
    injection HE; intros; subst.
    rewrite Esp2 in MU, SB.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 80, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    pose proof (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel') SB) as SB'.
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
      - intros a k Hinb. exact Hinb.
      - exact Herr.
      - exact Hsn.
      - exact (resb_start (g_b g) (g_A g) Hres).
      - intros a Ha. apply Hstw. rewrite Esp. unfold SLOT_K, SLOT_STACK in Ha. exact Ha.
      - exact Hrel.
      - apply (sl_unch _ _ _ (g_S g - 65536) (g_S g) MU').
        intros x Hx0 O. destruct (Z_le_dec (g_S g - 80) x); destruct (Z_lt_dec x (g_S g)); try lia;
          exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr (g_regs g) 2) + -80)); [reflexivity|].
        rewrite Esp2. unfold fsp, SLOT_FRAME. f_equal.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - unfold saved_bytes, SLOT_SAVE. rewrite <- Hra. exact SB'. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x12d50) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 (g_k g + 1)) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g (g_L g) (g_A g) regs' m' (g_md g) regs' (g_k g + 1));
      [exact HFR | cbn [app]; apply Permutation_refl | reflexivity | reflexivity | reflexivity
      | rewrite E1; vm_compute; reflexivity | exact E10' | exact Hk |].
    intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 HK.
    rewrite E1. apply H1. exists res, L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact HF''|]. split; [exact HP''|].
    unfold rg. split; [exact Hres10|]. split; [exact Hres0|].
    split; [e01_rp RP Hx 18|]. split; [e01_rp RP Hx 9|]. split; [e01_rp RP Hx 19|].
    unfold KS.
    split; [e01_rp RP Hx 22|]. split; [e01_rp RP Hx 23|]. split; [e01_rp RP Hx 24|].
    split; [e01_rp RP Hx 25|]. split; [e01_rp RP Hx 26|].
    e01_rp RP Hx 27.
Qed.

End E01.
