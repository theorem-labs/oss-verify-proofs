(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 700 of its 746 lines of code are new or changed and 885 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase3SegA.v, with its module paths and module names changed; 842 of its 899 lines of code are new or changed and 689 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, piece D: from the cut C0_D (0x805a4,
   reac_boxreg_declare returned idx in a0) through the checks of fuzz_boxreg.c:225-283 that follow the call, to the
   cut C0_BC (0x80630, a placed row: bcmp (row MAC, ZERO, 6) returned 0) or to the cut C0_F (0x808f0, a refused
   declare: free (name) follows).
   The code (offsets from 0x7ffac):
   - 0x805a4 .. 0x805b8: idx is -1 or n_before (the slot 0x48), else abort (0x80fa4); idx < 0 goes to 0x808c4;
   - placed (idx = n): the UBSan overflow check of n + 1 (trap 0x80fac); the shadow byte of r->n (address in the slot
     0x40) must be 0; r->n (address in the slot 0x28) = n + 1, else abort; the UBSan index check idx <= 4 and the
     pointer-overflow check ~r >= 56 idx (trap 0x80fac); the shadow byte of the row's nch (r + 56 n + 12) must be 0;
     its nch = nch (s9), else abort; then bcmp (r + 56 n, ZERO, 6) at 0x8062c (lx_hyps' lh_bcmp through YCbq.v
     aj_bcmp_at), whose result is 0: the new row's MAC is zero (reac_boxreg_declare_inv.v decl_row_mac) and so are
     ZERO's six bytes (A_OBJ 4, BLxLib's blx_rom_bytes);
   - refused (idx = -1): the shadow byte of r->n must be 0; r->n = n_before, else abort; idx = (want < 0 ? -1 :
     n_before), else abort (0x808ec), which holds since a refused declare means want = -1
     (LLVMFuzzerTestOneInput_case0.v c0_link_refused); then the cut F.
   Every abort and trap is refuted from the declare post the cut C0_D carries (reac_boxreg_declare_c.v
   declare_refused / declare_placed and the bytes BoxregUpd.v new_row_bytes leaves: LLVMFuzzerTestOneInput_case0.v
   c0_decl_n / c0_decl_length / c0_row_bsub, reac_boxreg_declare_inv.v decl_row_nch) and the registry invariant.
   The piece writes no byte of the walk's memory (only the bcmp interceptor writes, below sp1). The engine runs on
   small symbolic states, one per straight-line run, with read-only regions (the shape BoxBLxCase2.v measured): each
   shadow byte the walk loads is a region of its own at an atom that holds its address. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC85 BoxBCJ.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBReacBoxregFind.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs BoxBLxCase0Kit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd reac_boxreg_declare_c
  reac_boxreg_declare_inv LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn read_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS : AR_laws SEGS B := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma c0d_ewR : forall (regs : bvmap 5 word) extra n (rr : bv 5),
  Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs extra)) n = getr regs rr.
Proof.
intros regs extra n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Lemma c0d_rdword_range : forall (H : word -> bool) mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hr. unfold rdword in Hr.
repeat match type of Hr with context [aview SEGS H mem ?x] =>
  let b := fresh "b" in let Eb := fresh "Eb" in
  destruct (aview SEGS H mem x) as [b|] eqn:Eb; [|discriminate Hr];
  destruct (aview_byte SEGS H mem x b Eb) as (? & _ & _ & ?) end.
injection Hr as <-. lia.
Qed.

Lemma c0d_img_atom : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = w64 (VAL n).
Proof. intros E n HE Hn. unfold w64. rewrite <- (HE n Hn). symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma c0d_U_atom : forall E n z, ew E n = w64 z -> U E (SOff n 0) = z mod 2 ^ 64.
Proof.
intros E n z H. rewrite U_SOff, H, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_mod. lia.
Qed.

Lemma c0d_U_lit : forall E x, U E (SLit x) = x mod 2 ^ 64.
Proof. intros E x. rewrite U_SLit. reflexivity. Qed.

Lemma c0d_U_reg : forall E n w, ew E n = w -> U E (SOff n 0) = bv_unsigned w.
Proof.
intros E n w H. rewrite U_SOff, H, Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 w) as R.
change (bv_modulus 64) with (2 ^ 64) in R. unfold M64. lia.
Qed.

Lemma c0d_swrap : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
change (2 ^ 64 / 2) with (2 ^ 63). Z.div_mod_to_equations. lia.
Qed.

Lemma c0d_S_atom : forall E n z, ew E n = w64 z -> - 2 ^ 63 <= z < 2 ^ 63 -> Sg E (SOff n 0) = z.
Proof.
intros E n z H Hz. rewrite S_SOff, H, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned. rewrite bv_swrap_wrap.
apply c0d_swrap. exact Hz.
Qed.

Lemma c0d_den0 : forall E n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. Qed.

Lemma c0d_denv : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma c0d_blt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. reflexivity. Qed.

Lemma c0d_frame_ro : forall E rs m m', forallb (fun rg => YP09.r_whi rg <=? YP09.r_wlo rg) rs = true ->
  frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (rg & Hin & Ha).
rewrite forallb_forall in Hro. specialize (Hro rg Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma c0d_mod8 : forall a q, a mod q = 0 -> q mod 8 = 0 -> 0 < q -> a mod 8 = 0.
Proof.
intros a q Ha Hq Hq0. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hq; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [x Hx]. destruct Hq as [y Hy]. exists (x * y). lia.
Qed.

Lemma c0d_nth_le_bytes : forall m z k, (k < m)%nat ->
  nth k (Z_to_le_bytes m z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction m as [|m IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

(* The four bytes of a nonnegative 32-bit field at o: its little-endian bytes. *)
Lemma c0d_rd4_bytes : forall bs o, length bs = 288%nat -> 0 <= o -> o + 4 <= 288 -> 0 <= Boxreg.rd4 bs o ->
  forall k, (k < 4)%nat -> nth (Z.to_nat o + k) bs (Z_to_bv 8 0) = Z_to_bv 8 (le_byte (Boxreg.rd4 bs o) 4 k).
Proof.
intros bs o HL Ho1 Ho2 Hn k Hk.
assert (L : length (Boxreg.bsub bs o 4) = 4%nat) by (apply Boxreg.bsub_length; lia).
pose proof (Boxreg.rd4_range bs o) as Hr.
assert (Hv : bytes_le_to_Z (Boxreg.bsub bs o 4) = Boxreg.rd4 bs o).
{ pose proof (Boxreg.le4_range _ L) as R. unfold Boxreg.rd4 in *.
  revert Hn R. generalize (bytes_le_to_Z (Boxreg.bsub bs o 4)). intros v Hn R.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with (2 ^ 32) in *.
  change (2 ^ 32 / 2) with (2 ^ 31) in *. Z.div_mod_to_equations. lia. }
assert (E2 : nth (Z.to_nat o + k) bs (Z_to_bv 8 0) = nth k (Boxreg.bsub bs o 4) (Z_to_bv 8 0)).
{ unfold Boxreg.bsub. rewrite nth_firstn. change (Z.to_nat 4) with 4%nat.
  destruct (Nat.ltb_spec k 4); [|lia]. rewrite nth_skipn. try (f_equal; lia). }
rewrite E2. rewrite <- (BoxregRd.le_bytes_roundtrip (Boxreg.bsub bs o 4)). rewrite L, Hv.
rewrite c0d_nth_le_bytes by exact Hk.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small (Boxreg.rd4 bs o) (2 ^ 32)) by lia.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* A nonnegative 32-bit field of the registry, as the engine's 4-byte chunk reads it. *)
Lemma c0d_rd4_val : forall (W : world SEGS) (ms : machine_state) r bs o, lreg W ms r bs -> length bs = 288%nat ->
  0 <= o -> o + 4 <= 288 -> 0 <= Boxreg.rd4 bs o ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (r + o) 4 (Boxreg.rd4 bs o).
Proof.
intros W ms r bs o RG HL Ho1 Ho2 Hn kk Hkk.
assert (HA : aview SEGS (w_H W) (ms_mem ms) (r + (o + Z.of_nat kk)) =
  Some (bv_unsigned (nth (Z.to_nat o + kk) bs (Z_to_bv 8 0)))).
{ unfold lreg, lview in RG. rewrite RG by (unfold LX_REG; lia).
  replace (Z.to_nat (o + Z.of_nat kk)) with (Z.to_nat o + kk)%nat by lia. reflexivity. }
destruct (aview_byte SEGS _ _ _ _ HA) as (b & Hb & Hbv & _).
replace (r + o + Z.of_nat kk) with (r + (o + Z.of_nat kk)) by lia. rewrite Hb. f_equal.
replace b with (nth (Z.to_nat o + kk) bs (Z_to_bv 8 0)) by (apply bv_eq; lia).
exact (c0d_rd4_bytes bs o HL Ho1 Ho2 Hn kk Hkk).
Qed.

Section c.
(* ---- the cut D's data (0x805a4), fixed for the whole piece ---- *)
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Variable cx : lxcx.
Variables fp k acc : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable pos : nat.
Variables r fab op nm want : Z.
Variable bs : list byte.
Hypothesis HB : lx_base B MT cx.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].
Hypothesis HMO : mo_le MT (lc_S cx) S3 acc.
Hypothesis HNF : lx_from B MT POST (C0_F B MT i).
Hypothesis HNBC : lx_from B MT POST (C0_BC B MT i).
Hypothesis HF0 : c0_from B MT i cx fp k acc ly3 S3 W3 ms3 C0P_D pos r fab op nm bs.
Hypothesis S60 : lslot cx W3 ms3 0x60 nm.
Hypothesis HW : LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) want.
Hypothesis Hw : -1 <= want <= 40.
Hypothesis S20 : lslot cx W3 ms3 0x20 (want mod 2 ^ 64).
(* The geometry: the two stack pointers, the registry block, the frame F, the input block and the name block (from
   lx_base and AR at the cut; the piece moves none of them). *)
Hypothesis HGsp : lsp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= lsp0 cx <= 2 ^ 47 /\
  lsp0 cx - 287 <= lsp1 cx <= lsp0 cx - 256 /\ lsp1 cx mod 32 = 0.
Hypothesis HGr : r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ In (r, LX_REG) (ablocks B ly3 S3) /\
  in_app r 288.
Hypothesis HGF : 4096 <= lF cx fp /\ lF cx fp + 512 <= alloc_ceiling /\ lF cx fp mod 64 = 0 /\
  in_app (lF cx fp) 512 /\ frame_addr ly3 LX_CID fp = lF cx fp.
Hypothesis HGin : lc_n cx = 0 \/ (0 < lc_n cx /\ 4096 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling).
Hypothesis HGq : 4096 <= nm /\ nm + (c0_nk (lc_pl cx) pos + 1) <= alloc_ceiling.

#[local] Notation NCH := (c0_nchv (lc_pl cx) pos).
#[local] Notation BSE := (c0_basev (lc_pl cx) pos).
#[local] Notation NN := (Boxreg.bx_n bs).

(* The heap blocks the cut's facts read: the registry and the name. *)
Definition c0d_RS : list (Z * Z) := [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)].
(* A memory that keeps every byte the cut's facts read at D. *)
Definition c0d_K (m : word -> option byte) : Prop := c0_kept cx fp W3 [] c0d_RS (ms_mem ms3) m.
(* The journal of the piece at a memory m. *)
Definition c0d_J (m : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m md k.
(* The registers every point of the piece keeps. *)
Definition c0d_regs (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lsp1 cx) /\ getr regs 8 = w64 (lsp0 cx) /\ getr regs 9 = w64 (lsp1 cx) /\
  getr regs 3 = getr (lc_regs cx) 3 /\ getr regs 4 = getr (lc_regs cx) 4 /\
  getr regs 18 = w64 SHADOW_OFF /\ getr regs 22 = w64 (lSH cx fp) /\
  getr regs 20 = w64 r /\ getr regs 21 = w64 (lF cx fp + 64) /\ getr regs 27 = w64 fab.

Lemma c0d_K_refl : c0d_K (ms_mem ms3).
Proof. exact (c0_kept_refl cx fp W3 [] c0d_RS (ms_mem ms3)). Qed.

Lemma c0d_K_same : forall m m', c0d_K m -> (forall x, m' x = m x) -> c0d_K m'.
Proof.
intros m m' H E a Ha. rewrite <- (H a Ha). unfold aview, mbyte, mrestrict. rewrite E. reflexivity.
Qed.

Lemma c0d_Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47.
Proof. pose proof HGsp as (_ & Hs0 & Hs1 & _). pose proof asan_consts as (C1 & _). lia. Qed.

Lemma c0d_slot : forall (ms : machine_state) off v, c0d_K (ms_mem ms) -> 0 <= off -> off + 8 <= 0x98 ->
  lslot cx W3 ms3 off v -> lslot cx W3 ms off v.
Proof.
intros ms off v K H0 H1 Hv.
exact (c0_slot_keep cx fp W3 [] c0d_RS ms3 ms K c0d_Hsp off v H0 H1 (Forall_nil _) Hv).
Qed.

Lemma c0d_reg : forall (ms : machine_state) bs', c0d_K (ms_mem ms) -> lreg W3 ms3 r bs' -> lreg W3 ms r bs'.
Proof.
intros ms bs' K H. exact (c0_reg_keep cx fp W3 [] c0d_RS ms3 ms K r bs' ltac:(left; reflexivity) H).
Qed.

(* ---- the landing at F (0x808f0): a refused declare, the registry unchanged ---- *)
Lemma c0d_F_pt : forall regs m md,
  c0d_regs regs -> c0d_K m -> c0d_J m md -> lreg W3 ms3 r bs ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C0P_F)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27) K HJ HREG.
pose proof HF0 as (HCOM & HNM & HARG).
pose proof HCOM as (_ & _ & _ & HINV & HFAB & _).
apply (HNF cx fp k acc ly3 S3 W3 (mkst regs (Z_to_bv 64 (BASE + C0P_F)) m (seg_rom SEGS)) md HB HJ HFR HMO).
destruct (c0_land B MT i cx fp k acc ly3 S3 W3 ms3 m regs C0P_D C0P_F pos r fab op nm bs [] c0d_RS HB HCOM HNM
  (Forall_nil _) ltac:(right; left; reflexivity) K G2 G8 G9 G3 G4 G18 G22 G20 G21 G27) as [HC HN].
exists pos, r, fab, op, nm, bs, bs.
split; [exact HC|]. split; [exact HN|].
split; [exact (c0d_slot (mkst regs (Z_to_bv 64 (BASE + C0P_F)) m (seg_rom SEGS)) 0x60 nm K ltac:(lia) ltac:(lia) S60)|].
split; [exact (c0d_reg (mkst regs (Z_to_bv 64 (BASE + C0P_F)) m (seg_rom SEGS)) bs K HREG)|].
split; [exact HINV|]. split; [exact HFAB|].
intros j _. repeat split; right; reflexivity.
Qed.

(* ---- the landing at BC (0x80630): a placed row, bcmp of its MAC with ZERO returned 0 ---- *)
Lemma c0d_BC_pt : forall regs m md b p,
  c0d_regs regs -> c0d_K m -> c0d_J m md ->
  reac_boxreg_declare_c.declare_placed bs NCH BSE b p ->
  lreg W3 ms3 r (c0_placed bs b NCH p (c0_gs (lc_pl cx) pos op)) ->
  getr regs 10 = w64 0 -> getr regs 19 = w64 NN -> getr regs 23 = w64 (r + 56 * NN) ->
  getr regs 24 = w64 (Z.land op 8) -> getr regs 25 = w64 NCH -> getr regs 26 = w64 BSE ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C0P_BC)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md b p (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27) K HJ HPL HREG G10 G19 G23 G24 G25 G26.
pose proof HF0 as (HCOM & HNM & HARG).
pose proof HARG as (_ & _ & _ & S50).
apply (HNBC cx fp k acc ly3 S3 W3 (mkst regs (Z_to_bv 64 (BASE + C0P_BC)) m (seg_rom SEGS)) md HB HJ HFR HMO).
destruct (c0_land B MT i cx fp k acc ly3 S3 W3 ms3 m regs C0P_D C0P_BC pos r fab op nm bs [] c0d_RS HB HCOM HNM
  (Forall_nil _) ltac:(right; left; reflexivity) K G2 G8 G9 G3 G4 G18 G22 G20 G21 G27) as [HC HN].
exists pos, r, fab, op, nm, want, b, p, bs.
split; [exact HC|]. split; [exact HN|].
split; [exact G25|]. split; [exact G26|].
split; [exact (c0d_slot (mkst regs (Z_to_bv 64 (BASE + C0P_BC)) m (seg_rom SEGS)) 0x50 _ K ltac:(lia) ltac:(lia) S50)|].
split; [exact (c0d_slot (mkst regs (Z_to_bv 64 (BASE + C0P_BC)) m (seg_rom SEGS)) 0x60 nm K ltac:(lia) ltac:(lia) S60)|].
split; [exact HW|]. split; [exact Hw|].
split; [exact (c0d_slot (mkst regs (Z_to_bv 64 (BASE + C0P_BC)) m (seg_rom SEGS)) 0x20 _ K ltac:(lia) ltac:(lia) S20)|].
split; [exact G24|]. split; [exact HPL|].
split; [exact (c0d_reg (mkst regs (Z_to_bv 64 (BASE + C0P_BC)) m (seg_rom SEGS)) _ K HREG)|].
split; [exact G10|]. split; [exact G19 | exact G23].
Qed.

(* ---- the engine's small states ---- *)
Lemma c0d_seat : forall (regs : bvmap 5 word) extra m pc rs G,
  regions_wf rs = true -> Forall (region_ok SEGS (Eimg (Ereg regs extra)) (mrestrict (w_H W3) m)) rs ->
  pairwise_disjoint (Eimg (Ereg regs extra)) rs -> facts_ok (Eimg (Ereg regs extra)) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) (mkSS pc sr_atoms rs None G)
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
intros regs extra m pc rs G Hwf Hok Hd HG. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hok | exact Hd | exact HG].
Qed.

(* A read-only spill slot of the machine frame, at the atom of s1 (= sp1). *)
Definition c0d_rs (off : Z) (e : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) off (off + 8) 0 0 [YP09.mkChunk off (CVal 8 e)].
(* A shadow byte 0 at the atom a. *)
Definition c0d_sh (a : nat) : YP09.region := YP09.mkRegion (Some a) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
(* r->n (r = s4 = atom 20) as the atom a. *)
Definition c0d_rn (a : nat) : YP09.region :=
  YP09.mkRegion (Some 20%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SOff a 0))].
(* The fact on sp1 the engine's loads at s1 use. *)
Definition C0D_AF9 : nat * afact := (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5).

Definition c0d_ms (m : word -> option byte) : machine_state := mkst (lc_regs cx) (Z_to_bv 64 0) m (seg_rom SEGS).

Lemma c0d_rs_ok : forall E m off e v, bv_unsigned (ew E 9) = lsp1 cx ->
  c0d_K m -> lslot cx W3 ms3 off v -> sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= off -> off + 8 <= 0x98 ->
  region_ok SEGS E (mrestrict (w_H W3) m) (c0d_rs off e).
Proof.
intros E m off e v H9 K Hs He Hv H0 H1. pose proof HGsp as (_ & Hs0 & Hs1 & _).
pose proof (c0d_slot (c0d_ms m) off v K H0 H1 Hs) as Hs'.
unfold lslot, lview, c0d_ms in Hs'. cbn [ms_mem mkst] in Hs'.
unfold region_ok, c0d_rs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (lsp1 cx) off 8 e v He); [cbn; lia | cbn; lia |].
apply (val_mem_of_rdword SEGS (w_H W3) m). exact Hs'.
Qed.

Lemma c0d_af9 : forall E, bv_unsigned (ew E 9) = lsp1 cx -> afact_ok E (fst C0D_AF9) (snd C0D_AF9).
Proof.
intros E H9. pose proof HGsp as (_ & Hs0 & Hs1 & Hs32). pose proof asan_consts as (C1 & _).
unfold afact_ok, C0D_AF9. cbn [fst snd af_lo af_hi af_al2]. rewrite H9. change (2 ^ 5) with 32.
split; [lia|]. split; [exact Hs32 | lia].
Qed.

(* r->n's shadow byte (the slot 0x40 holds its address) is 0: the block's granule r + 280 .. r + 287 is whole. *)
Lemma c0d_sa : shadow_addr (r + 280) = SHADOW_OFF + r / 8 + 35 /\
  (r + 288 <= shadow_addr (r + 280) \/ shadow_addr (r + 280) + 1 <= r) /\ shadow_addr (r + 280) + 1 <= alloc_ceiling.
Proof.
pose proof HGr as (Hr16 & Hr0 & Hr1 & _ & Happ). pose proof asan_consts as (C1 & _).
assert (Hr8 : r mod 8 = 0) by (apply (c0d_mod8 _ 16); [exact Hr16 | reflexivity | lia]).
assert (E : shadow_addr (r + 280) = SHADOW_OFF + r / 8 + 35).
{ unfold shadow_addr. pose proof (Z.div_mod r 8 ltac:(lia)) as D. rewrite Hr8, Z.add_0_r in D.
  rewrite D at 1. replace (8 * (r / 8) + 280) with ((r / 8 + 35) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (D0 : 0 <= r / 8) by (apply Z.div_pos; lia).
assert (D1 : 8 * (r / 8) <= r) by (apply Z.mul_div_le; lia).
split; [exact E|]. rewrite E. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF.
destruct Happ as [_ [Hlo | [Hhi1 Hhi2]]].
- assert (r / 8 <= 268430848) by (apply Z.div_le_upper_bound; lia). split; [left; lia | lia].
- assert (r / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). split; [right; lia | lia].
Qed.

Lemma c0d_ar : forall m md, c0d_J m md -> AR SEGS B ly3 S3 W3 m md.
Proof. intros m md HJ. exact (proj1 HJ). Qed.

Lemma c0d_sa_zero : forall m md, c0d_J m md -> aview SEGS (w_H W3) m (shadow_addr (r + 280)) = Some 0.
Proof.
intros m md HJ. pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & _).
destruct (al_shadow _ _ LAWS ly3 S3 W3 m md r LX_REG (c0d_ar m md HJ) Hin) as [(_ & _ & HBS) _].
change (req_size LX_REG) with 288 in HBS.
pose proof (HBS 35 ltac:(split; [lia | reflexivity])) as H35. change (35 <? 288 / 8) with true in H35.
rewrite (proj1 c0d_sa). unfold shadow_of_addr in H35. rewrite <- H35. f_equal; unfold SHADOW_OFF; lia.
Qed.

Lemma c0d_vm1 : forall m a, aview SEGS (w_H W3) m a = Some 0 -> val_mem SEGS (mrestrict (w_H W3) m) a 1 0.
Proof.
intros m a H kk Hkk. assert (kk = 0%nat) by lia. subst kk. rewrite Z.add_0_r.
destruct (aview_byte SEGS _ _ _ _ H) as (b & Hb & Hbv & _). rewrite Hb. f_equal. apply bv_eq.
rewrite <- Hbv. reflexivity.
Qed.

Lemma c0d_sh_ok : forall E m md n a, c0d_J m md -> bv_unsigned (ew E n) = a -> aview SEGS (w_H W3) m a = Some 0 ->
  0 <= a -> a + 1 <= 2 ^ 64 -> region_ok SEGS E (mrestrict (w_H W3) m) (c0d_sh n).
Proof.
intros E m md n a HJ Hn Ha H0 H1.
unfold region_ok, c0d_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hn. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. apply (chunk_ok_val SEGS E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact (c0d_vm1 m _ Ha).
Qed.

Lemma c0d_rn_ok : forall E m a bs', bv_unsigned (ew E 20) = r -> ew E a = w64 (Boxreg.bx_n bs') ->
  c0d_K m -> lreg W3 ms3 r bs' -> length bs' = 288%nat -> 0 <= Boxreg.bx_n bs' < 2 ^ 31 ->
  region_ok SEGS E (mrestrict (w_H W3) m) (c0d_rn a).
Proof.
intros E m a bs' H20 Ha K RG HL Hn. pose proof HGr as (Hr16 & Hr0 & Hr1 & _).
pose proof asan_consts as (C1 & _).
unfold region_ok, c0d_rn. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. apply (chunk_ok_val SEGS E _ _ 280 4 (SOff a 0) (Boxreg.bx_n bs'));
  [exact (c0d_den0 E a _ Ha) | cbn; lia | cbn; lia |].
pose proof (c0d_reg (c0d_ms m) bs' K RG) as RG'.
exact (c0d_rd4_val W3 (c0d_ms m) r bs' 280 RG' HL ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_n in Hn; lia)).
Qed.

(* ---- R: a refused declare (idx = -1), 0x805a4 .. 0x808f0 ---- *)
Definition C0D_SB : Z := 0x7fff8000.
Definition C0D_Bx : sv := SLit C0D_SB.
Definition C0D_span : Z * Z := (C0D_SB, C0D_SB + 2 ^ 44 - 1).
Definition ss_R : sstate := mkSS C0P_D sr_atoms
  [c0d_rs 0x40 (SOff 32 0); c0d_sh 32; c0d_rs 0x20 (SOff 34 0); c0d_rs 0x28 (SOff 20 280); c0d_rn 33;
   c0d_rs 0x48 (SOff 33 0)] None
  (mkFacts [C0D_AF9; (20%nat, mkAF 4096 (2 ^ 47) 4); (33%nat, mkAF 0 5 0)] [] []).

Ltac c0d_ro K :=
  lazymatch type of K with c0d_K ?m0 =>
  match goal with HF : frame_of _ ?rs m0 ?m1 |- _ =>
    let H := fresh "K" in
    pose proof (c0d_K_same m0 m1 K (c0d_frame_ro _ rs m0 m1 eq_refl HF)) as H; clear K; rename H into K
  end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Lemma c0d_regs_same : forall regs regs',
  (forall n, In n [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] -> getr regs' (Z_to_bv 5 n) = getr regs (Z_to_bv 5 n)) ->
  c0d_regs regs -> c0d_regs regs'.
Proof.
intros regs regs' K (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27). unfold c0d_regs.
split; [etransitivity; [exact (K 2 ltac:(cbn; tauto)) | exact G2]|].
split; [etransitivity; [exact (K 8 ltac:(cbn; tauto)) | exact G8]|].
split; [etransitivity; [exact (K 9 ltac:(cbn; tauto)) | exact G9]|].
split; [etransitivity; [exact (K 3 ltac:(cbn; tauto)) | exact G3]|].
split; [etransitivity; [exact (K 4 ltac:(cbn; tauto)) | exact G4]|].
split; [etransitivity; [exact (K 18 ltac:(cbn; tauto)) | exact G18]|].
split; [etransitivity; [exact (K 22 ltac:(cbn; tauto)) | exact G22]|].
split; [etransitivity; [exact (K 20 ltac:(cbn; tauto)) | exact G20]|].
split; [etransitivity; [exact (K 21 ltac:(cbn; tauto)) | exact G21]|].
etransitivity; [exact (K 27 ltac:(cbn; tauto)) | exact G27].
Qed.

Lemma c0d_regs_pres : forall regs regs', aregs_preserved regs regs' -> c0d_regs regs -> c0d_regs regs'.
Proof.
intros regs regs' HP. apply c0d_regs_same. intros n Hn. apply HP. unfold acallee_saved.
cbv [In] in Hn. lia.
Qed.

Lemma c0d_regs_run : forall regs extra ss (ms : machine_state),
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) ss (restrict (w_H W3) ms) ->
  forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0))
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) = true ->
  c0d_regs regs -> c0d_regs (ms_regs ms).
Proof.
intros regs extra ss ms HS Hl. apply c0d_regs_same. intros n Hn.
apply (regs_kept_of_st_ok_pi _ ss (restrict (w_H W3) ms) regs extra (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) HS);
  [| exact Hl | apply in_map; exact Hn].
split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma c0d_regs_call : forall regs extra ss (ms : machine_state),
  st_ok SEGS (Eimg (Ereg regs extra)) ss (restrict (w_H W3) ms) ->
  forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0))
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) = true ->
  c0d_regs regs -> c0d_regs (ms_regs ms).
Proof.
intros regs extra ss ms HS Hl. apply c0d_regs_same. intros n Hn.
pose proof (regs_kept_of_st_ok SEGS _ ss (restrict (w_H W3) ms) regs extra
  (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) HS) as K.
cbn [restrict ms_regs] in K. apply K; [| exact Hl | apply in_map; exact Hn].
split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma c0d_R : forall regs m md,
  c0d_regs regs -> getr regs 10 = w64 (-1) -> c0d_K m -> c0d_J m md -> lreg W3 ms3 r bs ->
  reac_boxreg_declare_c.declare_refused bs NCH BSE ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C0P_D)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md GR G10 K HJ HREG HRF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & Happ).
pose proof asan_consts as (C1 & _).
pose proof c0d_sa as (ESA & HSA1 & HSA2).
pose proof HF0 as (HCOM & HNM & HARG).
pose proof HCOM as (_ & _ & _ & HINV & HFAB & _ & _ & _ & SL & _ & S48 & _).
pose proof SL as (_ & S28 & _ & _ & S40 & _ & _ & _).
pose proof HINV as ((HLbs & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
pose proof (LLVMFuzzerTestOneInput_case0.c0_link_refused bs NCH BSE want HW HRF) as Hwm.
set (ex := [w64 (shadow_addr (r + 280)); w64 NN; w64 (want mod 2 ^ 64)]).
set (E := Eimg (Ereg regs ex)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j ex (w64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs ex j). }
assert (F32 : ew E 32 = w64 (shadow_addr (r + 280))) by exact (EX 0%nat ltac:(lia)).
assert (F33 : ew E 33 = w64 NN) by exact (EX 1%nat ltac:(lia)).
assert (F34 : ew E 34 = w64 (want mod 2 ^ 64)) by exact (EX 2%nat ltac:(lia)).
assert (U9 : bv_unsigned (ew E 9) = lsp1 cx) by (unfold E; rewrite (c0d_ewR regs ex 9 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (F20 : ew E 20 = w64 r) by (unfold E; rewrite (c0d_ewR regs ex 20 20%bv eq_refl); exact G20).
assert (U20 : bv_unsigned (ew E 20) = r) by (rewrite F20; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = shadow_addr (r + 280)) by (rewrite F32; apply unsigned_lit_small; unfold SHADOW_OFF in ESA; lia).
assert (U33 : bv_unsigned (ew E 33) = NN) by (rewrite F33; apply unsigned_lit_small; lia).
assert (F10 : ew E 10 = w64 (-1)) by (unfold E; rewrite (c0d_ewR regs ex 10 10%bv eq_refl); exact G10).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HE : E = Eimg (Ereg regs ex)) by reflexivity.
clearbody E ex.
assert (HS : st_ok_pi SEGS VAL E ss_R (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + C0P_D)) m (seg_rom SEGS)))).
{ rewrite HE. apply c0d_seat; [vm_compute; reflexivity | | | ]; rewrite <- HE.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (c0d_rs_ok E m 0x40 (SOff 32 0) (shadow_addr (r + 280)) U9 K S40 (c0d_den0 E 32 _ F32)); unfold SHADOW_OFF in ESA; lia.
    + apply (c0d_sh_ok E m md 32 (shadow_addr (r + 280)) HJ U32 (c0d_sa_zero m md HJ)); unfold SHADOW_OFF in ESA; lia.
    + apply (c0d_rs_ok E m 0x20 (SOff 34 0) (want mod 2 ^ 64) U9 K S20 (c0d_den0 E 34 _ F34)); [apply Z.mod_pos_bound; lia | lia | lia].
    + apply (c0d_rs_ok E m 0x28 (SOff 20 280) (r + 280) U9 K S28); [| lia | lia | lia].
      exact (c0d_denv E 20 r 280 F20 ltac:(lia)).
    + exact (c0d_rn_ok E m 33 bs U20 F33 K HREG HLbs ltac:(lia)).
    + apply (c0d_rs_ok E m 0x48 (SOff 33 0) NN U9 K S48 (c0d_den0 E 33 _ F33)); lia.
  - unfold c0d_rs, c0d_sh, c0d_rn. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. repeat split; unfold YP09.extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U20, ?U32; unfold SHADOW_OFF in ESA; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [exact (c0d_af9 E U9)|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16; split; [lia|]; split; [exact Hr16 | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U33; rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I]. }
assert (SHOK : sh_ok SEGS C0D_Bx [] E (mrestrict (w_H W3) m)) by constructor.
unfold c0d_J in HJ.
paj_run_tok RUN HS HJ SHOK C0D_span; [awr_ok_tac |].

c0d_ro K.
psrr_branch_tok RUN BR HS SHOK C0D_span; rewrite branch_eq_U, (c0d_U_atom E 10 (-1) F10), c0d_U_lit in Hc.

2: { vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK C0D_span; [awr_ok_tac |]. c0d_ro K.
psrr_branch_tok RUN BR HS SHOK C0D_span; rewrite c0d_blt, (c0d_S_atom E 10 (-1) F10 ltac:(lia)), S_SLit in Hc;
  change (bv_swrap 64 0) with 0 in Hc.
2: { vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK C0D_span; [awr_ok_tac |]. c0d_ro K.

assert (UOR : U E (SAlu ALU_OR (SAluw ALU_SRA (SOff 34 0) (SLit 31)) (SOff 33 0)) = 2 ^ 64 - 1).
{ unfold U. cbn [sv_denot]. rewrite F34, F33, Hwm. rewrite !Z.add_0_r.
  replace (sext 64 (alu32 ALU_SRA (low32 (Z_to_bv 64 (bv_unsigned (w64 (-1 mod 2 ^ 64))))) (low32 (Z_to_bv 64 31))))
    with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity).
  unfold alu64, alu. rewrite bv_or_unsigned. change (bv_unsigned (Z_to_bv 64 18446744073709551615)) with 18446744073709551615.
  rewrite LLVMFuzzerTestOneInput_case0.c0_lor1. reflexivity. }
psrr_branch_tok RUN BR HS SHOK C0D_span; rewrite branch_ne_U, (c0d_U_atom E 10 (-1) F10), UOR in Hc.
1: { vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK C0D_span C0P_F; [awr_ok_tac |]. c0d_ro K.

pmkst HS. rewrite HE in HS.
exact (c0d_F_pt _ _ _ (c0d_regs_run _ _ _ _ HS eq_refl GR) K HJ HREG).
Qed.

(* ---- P: a placed row (idx = n), 0x805a4 .. 0x8060c (the shadow check of the row's nch) ---- *)
Definition ss_P : sstate := mkSS C0P_D sr_atoms
  [c0d_rs 0x48 (SOff 10 0); c0d_rs 0x40 (SOff 32 0); c0d_sh 32; c0d_rs 0x28 (SOff 20 280); c0d_rn 33;
   c0d_rs 0x70 (SOff 34 0)] None
  (mkFacts [C0D_AF9; (20%nat, mkAF 4096 (2 ^ 47) 4); (10%nat, mkAF 0 4 0); (33%nat, mkAF 1 5 0)] [] []).

(* The row r + 56 n and its nch field, as the engine computes them from a0 = n (0x805e8 .. 0x80608). *)
Lemma c0d_rw_val : forall E n, ew E 10 = w64 n -> ew E 20 = w64 r -> 0 <= n <= 4 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 56)) (SOff 20 0)) = w64 (r + 56 * n).
Proof.
intros E n H10 H20 Hn. pose proof HGr as (_ & Hr0 & Hr1 & _). pose proof asan_consts as (C1 & _).
rewrite denot_lit_U, U_SAlu, U_SMd, (c0d_U_atom E 10 n H10), (c0d_U_atom E 20 r H20), c0d_U_lit.
cbn [zalu_raw zmd_raw]. rewrite (Z.mod_small n), (Z.mod_small 56), (Z.mod_small r) by lia.
unfold zcanon, M64. rewrite (Z.mod_small (n * 56)) by lia. rewrite (Z.mod_small (n * 56 + r)) by lia.
unfold w64. f_equal. lia.
Qed.

Lemma c0d_rw12_U : forall E n, ew E 10 = w64 n -> ew E 20 = w64 r -> 0 <= n <= 4 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 56)) (SLit 12)) (SOff 20 0)) = r + 56 * n + 12.
Proof.
intros E n H10 H20 Hn. pose proof HGr as (_ & Hr0 & Hr1 & _). pose proof asan_consts as (C1 & _).
rewrite !U_SAlu, U_SMd, (c0d_U_atom E 10 n H10), (c0d_U_atom E 20 r H20), !c0d_U_lit.
cbn [zalu_raw zmd_raw]. rewrite (Z.mod_small n), (Z.mod_small 56), (Z.mod_small 12), (Z.mod_small r) by lia.
unfold zcanon, M64. rewrite (Z.mod_small (n * 56)) by lia. rewrite (Z.mod_small (n * 56 + 12)) by lia.
rewrite (Z.mod_small (n * 56 + 12 + r)) by lia. lia.
Qed.

Lemma c0d_rw12_val : forall E n, ew E 10 = w64 n -> ew E 20 = w64 r -> 0 <= n <= 4 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 56)) (SLit 12)) (SOff 20 0)) = w64 (r + 56 * n + 12).
Proof. intros E n H10 H20 Hn. rewrite denot_lit_U, (c0d_rw12_U E n H10 H20 Hn). reflexivity. Qed.

Lemma c0d_rwsh_val : forall E n, ew E 10 = w64 n -> ew E 20 = w64 r -> ew E 18 = w64 SHADOW_OFF -> 0 <= n <= 4 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 56)) (SLit 12))
    (SOff 20 0)) (SLit 3)) (SOff 18 0)) = w64 (shadow_addr (r + 56 * n + 12)).
Proof.
intros E n H10 H20 H18 Hn. pose proof HGr as (_ & Hr0 & Hr1 & _). pose proof asan_consts as (C1 & _).
rewrite denot_lit_U, U_SAlu, U_SAlu, (c0d_rw12_U E n H10 H20 Hn), (c0d_U_atom E 18 SHADOW_OFF H18), c0d_U_lit.
cbn [zalu_raw]. change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (D0 : 0 <= (r + 56 * n + 12) / 8) by (apply Z.div_pos; lia).
assert (D1 : (r + 56 * n + 12) / 8 <= r + 56 * n + 12) by (apply Z.div_le_upper_bound; lia).
unfold shadow_addr, SHADOW_OFF, zcanon, M64. rewrite (Z.mod_small 2147450880) by lia.
rewrite (Z.mod_small ((r + 56 * n + 12) / 8)) by lia. rewrite Z.mod_small by lia. unfold w64. f_equal. lia.
Qed.

(* The row's shadow byte: the granule r + 56 n + 8 .. r + 56 n + 15 of the registry block is whole. *)
Lemma c0d_rsa : forall n, 0 <= n <= 4 ->
  shadow_addr (r + 56 * n + 12) = SHADOW_OFF + r / 8 + (7 * n + 1) /\
  (r + 288 <= shadow_addr (r + 56 * n + 12) \/ shadow_addr (r + 56 * n + 12) + 1 <= r) /\
  shadow_addr (r + 56 * n + 12) + 1 <= alloc_ceiling.
Proof.
intros n Hn. pose proof HGr as (Hr16 & Hr0 & Hr1 & _ & Happ). pose proof asan_consts as (C1 & _).
assert (Hr8 : r mod 8 = 0) by (apply (c0d_mod8 _ 16); [exact Hr16 | reflexivity | lia]).
assert (E : shadow_addr (r + 56 * n + 12) = SHADOW_OFF + r / 8 + (7 * n + 1)).
{ unfold shadow_addr. pose proof (Z.div_mod r 8 ltac:(lia)) as D. rewrite Hr8, Z.add_0_r in D.
  rewrite D at 1. replace (8 * (r / 8) + 56 * n + 12) with (4 + (r / 8 + 7 * n + 1) * 8) by lia.
  rewrite Z.div_add by lia. change (4 / 8) with 0. lia. }
assert (D0 : 0 <= r / 8) by (apply Z.div_pos; lia).
assert (D1 : 8 * (r / 8) <= r) by (apply Z.mul_div_le; lia).
split; [exact E|]. rewrite E. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF.
destruct Happ as [_ [Hlo | [Hhi1 Hhi2]]].
- assert (r / 8 <= 268430848) by (apply Z.div_le_upper_bound; lia). split; [left; lia | lia].
- assert (r / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). split; [right; lia | lia].
Qed.

Lemma c0d_rsa_zero : forall m md n, c0d_J m md -> 0 <= n <= 4 ->
  aview SEGS (w_H W3) m (shadow_addr (r + 56 * n + 12)) = Some 0.
Proof.
intros m md n HJ Hn. pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & _).
destruct (al_shadow _ _ LAWS ly3 S3 W3 m md r LX_REG (c0d_ar m md HJ) Hin) as [(_ & _ & HBS) _].
change (req_size LX_REG) with 288 in HBS.
pose proof (HBS (7 * n + 1) ltac:(change ((288 + 7) / 8) with 36; lia)) as H1.
replace (7 * n + 1 <? 288 / 8) with true in H1 by (symmetry; apply Z.ltb_lt; change (288 / 8) with 36; lia).
rewrite (proj1 (c0d_rsa n Hn)). unfold shadow_of_addr in H1. rewrite <- H1. f_equal; unfold SHADOW_OFF; lia.
Qed.

(* ---- the table a placed declare leaves: r->n = n + 1, the row's nch and its zero MAC ---- *)
Definition c0d_PL (b p : Z) : list byte := c0_placed bs b NCH p (c0_gs (lc_pl cx) pos op).

Lemma c0d_nch_rng : 0 <= NCH < 256.
Proof. exact (LLVMFuzzerTestOneInput_case0.c0_nch_range (c0_pl0 (lc_pl cx) pos)). Qed.

Lemma c0d_pl_facts : forall b p, reac_boxreg_declare_c.declare_placed bs NCH BSE b p ->
  0 <= NN <= 4 /\ length (c0d_PL b p) = 288%nat /\ Boxreg.bx_n (c0d_PL b p) = NN + 1 /\
  Boxreg.rd4 (c0d_PL b p) (56 * NN + 12) = NCH /\
  (forall j, 0 <= j < 6 -> nth (Z.to_nat (56 * NN + j)) (c0d_PL b p) (Z_to_bv 8 0) = Z_to_bv 8 0).
Proof.
intros b p HPL. pose proof HF0 as (HCOM & _ & _). pose proof HCOM as (_ & _ & _ & HINV & _).
pose proof HINV as ((HLbs & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
pose proof HPL as (_ & Hn5 & _). pose proof c0d_nch_rng as HK.
assert (Hn4 : 0 <= NN <= 4) by lia.
change (c0d_PL b p) with (reac_boxreg_declare_c.decl_bytes bs b NCH p (c0_gs (lc_pl cx) pos op)).
split; [exact Hn4|].
split; [exact (LLVMFuzzerTestOneInput_case0.c0_decl_length bs b NCH p _ HLbs Hn4)|].
split; [exact (LLVMFuzzerTestOneInput_case0.c0_decl_n bs b NCH p _ HLbs Hn4)|].
split.
- apply BoxregUpd.rd4_le4; [lia|].
  rewrite (LLVMFuzzerTestOneInput_case0.c0_row_bsub bs b NCH p _ 12 4 HLbs Hn4) by lia.
  apply reac_boxreg_declare_inv.decl_row_nch.
- intros j Hj.
  pose proof (LLVMFuzzerTestOneInput_case0.c0_row_bsub bs b NCH p (c0_gs (lc_pl cx) pos op) 0 6 HLbs Hn4
    ltac:(lia) ltac:(lia) ltac:(lia)) as E6.
  rewrite reac_boxreg_declare_inv.decl_row_mac, Z.add_0_r in E6.
  assert (Hn : nth (Z.to_nat j) (Boxreg.bsub (reac_boxreg_declare_c.decl_bytes bs b NCH p (c0_gs (lc_pl cx) pos op))
    (56 * NN) 6) (Z_to_bv 8 0) = nth (Z.to_nat (56 * NN + j)) (reac_boxreg_declare_c.decl_bytes bs b NCH p
    (c0_gs (lc_pl cx) pos op)) (Z_to_bv 8 0)).
  { unfold Boxreg.bsub. rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat 6)); [|lia].
    rewrite nth_skipn. f_equal. lia. }
  rewrite <- Hn, E6. unfold Boxreg.zero6. apply nth_repeat.
Qed.

(* ---- the bcmp wrapper at 0x8062c: bcmp (r + 56 n, ZERO, 6) ---- *)
Lemma c0d_SH : lSH cx fp = SHADOW_OFF + lF cx fp / 8 /\ 0 <= lF cx fp / 8 /\ lSH cx fp + 64 <= alloc_ceiling.
Proof.
pose proof HGF as (HFl & HFc & HF64 & HFapp & _). pose proof asan_consts as (C1 & _).
assert (E : lSH cx fp = SHADOW_OFF + lF cx fp / 8) by reflexivity.
assert (D0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
assert (D1 : 8 * (lF cx fp / 8) <= lF cx fp) by (apply Z.mul_div_le; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF in *.
split; [exact E|]. split; [exact D0|].
destruct HFapp as [_ [Hlo | [Hhi1 Hhi2]]].
- assert (lF cx fp / 8 <= 268430848) by (apply Z.div_le_upper_bound; lia). lia.
- assert (lF cx fp / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

(* Every byte the cut's facts read lies at or above sp1, or below the allocator's ceiling (far below sp1). *)
Lemma c0d_kat_rng : forall a, c0_kat cx fp [] c0d_RS a -> 0 <= a < 2 ^ 64 /\ (a + 8192 < lsp1 cx \/ lsp1 cx <= a).
Proof.
intros a Ha. pose proof HGsp as (_ & Hs0 & Hs1 & _). pose proof HGF as (HFl & HFc & _).
pose proof HGr as (_ & Hr0 & Hr1 & _). pose proof HGq as (Hq0 & Hq1).
pose proof c0d_SH as (ESH & D0 & HSH1). pose proof asan_consts as (C1 & _).
pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hnk. fold (c0_nk (lc_pl cx) pos) in Hnk.
unfold SHADOW_OFF in ESH.
destruct Ha as [[H _] | [H | [H | [H | H]]]].
- split; lia.
- destruct HGin as [Hn0 | (Hn1 & Hp0 & Hp1)]; [unfold lc_n in *; lia | split; lia].
- split; lia.
- split; lia.
- unfold c0d_RS in H. apply Exists_exists in H as (q & Hq & Hqa).
  destruct Hq as [<- | [<- | []]]; cbn [fst snd] in Hqa; unfold LX_REG in Hqa; split; lia.
Qed.

Lemma c0d_K_bcmp : forall m m', c0d_K m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx - 8192 <= a < lsp1 cx) -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  c0d_K m'.
Proof.
intros m m' K Hfr a Ha. rewrite (Hfr a); [exact (K a Ha) | |]; destruct (c0d_kat_rng a Ha); lia.
Qed.

Lemma c0d_gptp : getr (lc_regs cx) 3 = w64 (as_gp B) /\ getr (lc_regs cx) 4 = w64 (as_tp B).
Proof. pose proof HB as ((_ & _ & _ & Hgp & Htp & _) & _). split; assumption. Qed.

Lemma c0d_o16 : (lsp1 cx - lsp0 cx) mod 16 = 0.
Proof.
pose proof HGsp as (Hs16 & _ & _ & Hs32).
apply Z.mod_divide in Hs16; [|lia]. apply Z.mod_divide in Hs32; [|lia]. apply Z.mod_divide; [lia|].
destruct Hs16 as [x Hx]. destruct Hs32 as [y Hy]. exists (2 * y - x). lia.
Qed.

(* ZERO (A_OBJ 4): its shadow byte (its size 6), its six zero bytes and where it lies. *)
Lemma c0d_gshadow : forall g sz m md, In (g, sz) LX_GLOBS -> c0d_J m md ->
  aview SEGS (w_H W3) m (shadow_addr (VAL (A_OBJ g))) = Some sz.
Proof.
intros g sz m md Hin HJ. destruct (c0d_ar m md HJ) as (M & _).
pose proof (am_const _ _ _ _ M) as C. rewrite Forall_forall in C.
assert (Hc : In (z1 (ANum (shadow_addr (VAL (A_OBJ g)))) sz) (as_const B ly3)).
{ apply (blx_cells B (lh_glob B MT HY) ly3). unfold lx_glob_cells. apply in_flat_map.
  exists (g, sz). split; [exact Hin|]. cbn [fst snd]. left. reflexivity. }
assert (Hsz : 0 <= sz < 256) by (cbv [LX_GLOBS In] in Hin; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]); destruct Hin).
specialize (C _ Hc). unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
specialize (C 0%nat ltac:(lia)). rewrite Z.add_0_r in C. rewrite C. f_equal.
unfold le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. exact Hsz.
Qed.

Lemma c0d_Z_bytes : forall m md j, c0d_J m md -> 0 <= j < 6 -> aview SEGS (w_H W3) m (VAL (A_OBJ 4) + j) = Some 0.
Proof.
intros m md j HJ Hj.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
pose proof (lx_arodata_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO) as HRO3.
destruct (blx_rom_bytes B (lh_glob B MT HY) (4%nat, [0; 0; 0; 0; 0; 0]) ltac:(cbn; tauto) j ltac:(cbn; lia))
  as (Hrom & Ho & He & Hb).
cbn [fst snd] in *. rewrite (HRO3 _ (or_introl Hrom) Ho He), Hb. f_equal.
assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) as [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia; reflexivity.
Qed.

Lemma c0d_Z_img : 4096 <= VAL (A_OBJ 4) /\ VAL (A_OBJ 4) + 6 <= alloc_ceiling /\ amem_range (VAL (A_OBJ 4)) 6.
Proof.
destruct (blx_marg B (lh_glob B MT HY) (4%nat, 6) ltac:(cbn; tauto)) as [M1 M2]. cbn [fst snd] in *.
pose proof asan_consts as (C1 & _). unfold IMG_HI in M2.
split; [lia|]. split; [lia|]. unfold amem_range, kLowMemEnd. left. lia.
Qed.

Lemma c0d_Z_ra : forall m md, c0d_J m md -> range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (VAL (A_OBJ 4)) 6.
Proof.
intros m md HJ. apply range_addressable_partial; [exact (c0d_gshadow 4 6 m md ltac:(cbn; tauto) HJ) | | lia].
apply (c0d_mod8 _ 32); [exact (blx_al B (lh_glob B MT HY) (4%nat, 6) ltac:(cbn; tauto)) | reflexivity | lia].
Qed.

Lemma c0d_Z_hull : forall m md, c0d_J m md -> shadow_hull_vis (aview SEGS (w_H W3) m) (VAL (A_OBJ 4)) 6.
Proof.
intros m md HJ. destruct (blx_marg B (lh_glob B MT HY) (4%nat, 6) ltac:(cbn; tauto)) as [M1 M2]. cbn [fst snd] in *.
eapply ro_hull; [exact (blx_isv B (lh_glob B MT HY)) | exact (c0d_ar m md HJ) | lia | exact M1 | exact M2].
Qed.

Lemma c0d_bcmp : forall (regsT : bvmap 5 word) memT mdT b p,
  c0d_regs regsT -> c0d_K memT -> c0d_J memT mdT ->
  reac_boxreg_declare_c.declare_placed bs NCH BSE b p -> lreg W3 ms3 r (c0d_PL b p) ->
  getr regsT 10 = w64 (r + 56 * NN) -> getr regsT 11 = w64 (VAL (A_OBJ 4)) -> getr regsT 12 = w64 6 ->
  getr regsT 1 = Z_to_bv 64 (BASE + C0P_BC) ->
  getr regsT 19 = w64 NN -> getr regsT 23 = w64 (r + 56 * NN) -> getr regsT 24 = w64 (Z.land op 8) ->
  getr regsT 25 = w64 NCH -> getr regsT 26 = w64 BSE ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
    (POST cx).
Proof.
intros regsT memT mdT b p GR K HJ HPL HREG H10 H11 H12 Hra G19 G23 G24 G25 G26.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & _).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof asan_consts as (C1 & _).
pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & _).
pose proof c0d_gptp as (Hgp & Htp).
pose proof (c0d_pl_facts b p HPL) as (Hn4 & HLPL & HNPL & HNCH & HMAC).
pose proof c0d_Z_img as (Z0 & Z1 & ZM).
pose proof (c0d_ar memT mdT HJ) as HAR.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hrq : req_size LX_REG = 288) by reflexivity.
assert (Hsp : spZ regsT = lsp0 cx + (lsp1 cx - lsp0 cx)).
{ unfold spZ. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
pose proof (c0d_reg (c0d_ms memT) _ K HREG) as RG. unfold lreg, lview, c0d_ms in RG. cbn [ms_mem mkst] in RG.
assert (RB : forall q, 0 <= q < 6 -> aview SEGS (w_H W3) memT (r + 56 * NN + q) = Some 0).
{ intros q Hq. replace (r + 56 * NN + q) with (r + (56 * NN + q)) by lia.
  rewrite RG by (unfold LX_REG; lia). rewrite (HMAC q Hq). reflexivity. }
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ (lh_bcmp B MT HY) W3 regsT memT LX_STK (lsp0 cx) []
    (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 mdT k (r + 56 * NN) (VAL (A_OBJ 4)) 6
    (lsp1 cx - lsp0 cx) _ HJ H10 H11 H12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp c0d_o16
    ltac:(lia) ltac:(unfold LX_STK; rewrite Hes; lia) ltac:(rewrite G3; exact Hgp) ltac:(rewrite G4; exact Htp)
    Hra (ret_ok_codeptr_v C0P_BC ltac:(unfold C0P_BC; lia) eq_refl)).
  - intros a Ha. split; [|rewrite Hsp, Hes; lia].
    replace a with (r + 56 * NN + (a - (r + 56 * NN))) by lia. rewrite RB by lia. discriminate.
  - intros a Ha. split; [|rewrite Hsp, Hes; lia].
    replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia. rewrite (c0d_Z_bytes memT mdT) by (exact HJ || lia).
    discriminate.
  - intros a Ha. rewrite Hes. lia.
  - intros a Ha. rewrite Hes. lia.
  - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 memT mdT r LX_REG); [exact HAR | exact Hin | lia | rewrite Hrq; lia].
  - exact ZM.
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 memT mdT r LX_REG); [exact HAR | exact Hin | lia | rewrite Hrq; lia].
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 memT mdT r LX_REG);
      [exact HAR | exact Hin | lia | rewrite Hrq; lia | lia].
  - exact (c0d_Z_ra memT mdT HJ).
  - intros _. exact (c0d_Z_hull memT mdT HJ). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & _).
apply (c0d_BC_pt regs2 mem2 md2 b p (c0d_regs_pres regsT regs2 HP GR)).
- apply (c0d_K_bcmp memT mem2 K). intros a Ha Hwin. apply Hfr; [exact Ha | rewrite Hes; lia].
- exact HJ2.
- exact HPL.
- exact HREG.
- rewrite Hv. apply Hcmp. intros q Hq. rewrite RB, (c0d_Z_bytes memT mdT q HJ Hq) by exact Hq. reflexivity.
- rewrite <- G19. exact (HP 19 ltac:(unfold acallee_saved; lia)).
- rewrite <- G23. exact (HP 23 ltac:(unfold acallee_saved; lia)).
- rewrite <- G24. exact (HP 24 ltac:(unfold acallee_saved; lia)).
- rewrite <- G25. exact (HP 25 ltac:(unfold acallee_saved; lia)).
- rewrite <- G26. exact (HP 26 ltac:(unfold acallee_saved; lia)).
Qed.

(* ---- P2: 0x8060c .. 0x8062c, the shadow check of the row's nch, nch, and the call bcmp (row, ZERO, 6) ---- *)
Definition C0P_R12 : Z := 0x660.  (* 0x8060c: lb of the row's nch's shadow byte *)
Definition c0d_rwr : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 25 0))].
Definition ss_P2 : sstate := mkSS C0P_R12 sr_atoms [c0d_sh 11; c0d_rwr] None (mkFacts [(25%nat, mkAF 0 255 0)] [] []).

Lemma c0d_P2 : forall regs m md b p,
  c0d_regs regs -> c0d_K m -> c0d_J m md ->
  reac_boxreg_declare_c.declare_placed bs NCH BSE b p -> lreg W3 ms3 r (c0d_PL b p) ->
  getr regs 10 = w64 (r + 56 * NN + 12) -> getr regs 11 = w64 (shadow_addr (r + 56 * NN + 12)) ->
  getr regs 19 = w64 NN -> getr regs 23 = w64 (r + 56 * NN) -> getr regs 24 = w64 (Z.land op 8) ->
  getr regs 25 = w64 NCH -> getr regs 26 = w64 BSE ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C0P_R12)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md b p GR K HJ HPL HREG G10 G11 G19 G23 G24 G25 G26.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & Happ). pose proof asan_consts as (C1 & _).
pose proof (c0d_pl_facts b p HPL) as (Hn4 & HLPL & HNPL & HNCH & HMAC).
pose proof (c0d_rsa NN Hn4) as (ERS & HRS1 & HRS2).
pose proof c0d_nch_rng as HK.
set (E := Eimg (Ereg regs (@nil word))).
assert (F10 : ew E 10 = w64 (r + 56 * NN + 12)) by (unfold E; rewrite (c0d_ewR regs [] 10 10%bv eq_refl); exact G10).
assert (U10 : bv_unsigned (ew E 10) = r + 56 * NN + 12) by (rewrite F10; apply unsigned_lit_small; lia).
assert (F11 : ew E 11 = w64 (shadow_addr (r + 56 * NN + 12))) by (unfold E; rewrite (c0d_ewR regs [] 11 11%bv eq_refl); exact G11).
assert (U11 : bv_unsigned (ew E 11) = shadow_addr (r + 56 * NN + 12))
  by (rewrite F11; apply unsigned_lit_small; unfold SHADOW_OFF in ERS; lia).
assert (F25 : ew E 25 = w64 NCH) by (unfold E; rewrite (c0d_ewR regs [] 25 25%bv eq_refl); exact G25).
assert (U25 : bv_unsigned (ew E 25) = NCH) by (rewrite F25; apply unsigned_lit_small; lia).
assert (F23 : ew E 23 = w64 (r + 56 * NN)) by (unfold E; rewrite (c0d_ewR regs [] 23 23%bv eq_refl); exact G23).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HE : E = Eimg (Ereg regs [])) by reflexivity.
clearbody E.
assert (HS : st_ok_pi SEGS VAL E ss_P2 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + C0P_R12)) m (seg_rom SEGS)))).
{ rewrite HE. apply c0d_seat; [vm_compute; reflexivity | | | ]; rewrite <- HE.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (c0d_sh_ok E m md 11 (shadow_addr (r + 56 * NN + 12)) HJ U11 (c0d_rsa_zero m md NN HJ Hn4));
        unfold SHADOW_OFF in ERS; lia.
    + unfold region_ok, c0d_rwr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 25 0) NCH);
        [exact (c0d_den0 E 25 _ F25) | cbn; lia | cbn; lia |].
      pose proof (c0d_reg (c0d_ms m) _ K HREG) as RG.
      pose proof (c0d_rd4_val W3 (c0d_ms m) r (c0d_PL b p) (56 * NN + 12) RG HLPL ltac:(lia) ltac:(lia)
        ltac:(rewrite HNCH; lia)) as V. rewrite HNCH in V. unfold c0d_ms in V. cbn [ms_mem mkst] in V.
      replace (r + 56 * NN + 12 + 0) with (r + (56 * NN + 12)) by lia. exact V.
  - unfold c0d_sh, c0d_rwr. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. repeat split; unfold YP09.extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U10, ?U11; unfold SHADOW_OFF in ERS; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U25; rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I]. }
assert (SHOK : sh_ok SEGS C0D_Bx [] E (mrestrict (w_H W3) m)) by constructor.
unfold c0d_J in HJ.
paj_run_tok RUN HS HJ SHOK C0D_span; [awr_ok_tac |]. c0d_ro K.

pmkst HS.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
prreg HS (19%bv : bv 5) Q19. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
rewrite HE in HS.
apply (c0d_bcmp _ _ _ b p (c0d_regs_call _ _ _ _ HS eq_refl GR) K HJ HPL HREG).
- rewrite Q10. exact F23.
- rewrite Q11. apply (c0d_img_atom _ _ HEI). unfold A_OBJ, A_TEXT, A_LIM; lia.
- rewrite Q12. reflexivity.
- rewrite Q1. reflexivity.
- rewrite Q19, HE, (c0d_ewR regs [] 19 19%bv eq_refl). exact G19.
- rewrite Q23. exact F23.
- rewrite Q24, HE, (c0d_ewR regs [] 24 24%bv eq_refl). exact G24.
- rewrite Q25. exact F25.
- rewrite Q26, HE, (c0d_ewR regs [] 26 26%bv eq_refl). exact G26.
Qed.

Lemma c0d_P1 : forall regs m md b p,
  c0d_regs regs -> getr regs 10 = w64 NN -> c0d_K m -> c0d_J m md ->
  getr regs 24 = w64 (Z.land op 8) -> getr regs 25 = w64 NCH -> getr regs 26 = w64 BSE ->
  reac_boxreg_declare_c.declare_placed bs NCH BSE b p ->
  lreg W3 ms3 r (c0d_PL b p) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C0P_D)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md b p GR G10 K HJ R24G R25G R26G HPL HREG.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & Happ).
pose proof asan_consts as (C1 & _).
pose proof c0d_sa as (ESA & HSA1 & HSA2).
pose proof HF0 as (HCOM & HNM & HARG).
pose proof HCOM as (_ & _ & _ & HINV & HFAB & _ & _ & _ & SL & _ & S48 & _).
pose proof SL as (_ & S28 & _ & _ & S40 & _ & S70 & _).
pose proof HINV as ((HLbs & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
pose proof HPL as (_ & Hn5 & _).
pose proof (c0d_pl_facts b p HPL) as (Hn4 & HLPL & HNPL & _ & _).
set (ex := [w64 (shadow_addr (r + 280)); w64 (NN + 1); w64 (2 ^ 64 - 1 - r)]).
set (E := Eimg (Ereg regs ex)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j ex (w64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs ex j). }
assert (F32 : ew E 32 = w64 (shadow_addr (r + 280))) by exact (EX 0%nat ltac:(lia)).
assert (F33 : ew E 33 = w64 (NN + 1)) by exact (EX 1%nat ltac:(lia)).
assert (F34 : ew E 34 = w64 (2 ^ 64 - 1 - r)) by exact (EX 2%nat ltac:(lia)).
assert (U9 : bv_unsigned (ew E 9) = lsp1 cx) by (unfold E; rewrite (c0d_ewR regs ex 9 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (F20 : ew E 20 = w64 r) by (unfold E; rewrite (c0d_ewR regs ex 20 20%bv eq_refl); exact G20).
assert (U20 : bv_unsigned (ew E 20) = r) by (rewrite F20; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = shadow_addr (r + 280)) by (rewrite F32; apply unsigned_lit_small; unfold SHADOW_OFF in ESA; lia).
assert (U33 : bv_unsigned (ew E 33) = NN + 1) by (rewrite F33; apply unsigned_lit_small; lia).
assert (F10 : ew E 10 = w64 NN) by (unfold E; rewrite (c0d_ewR regs ex 10 10%bv eq_refl); exact G10).
assert (U10 : bv_unsigned (ew E 10) = NN) by (rewrite F10; apply unsigned_lit_small; lia).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HE : E = Eimg (Ereg regs ex)) by reflexivity.
clearbody E ex.
assert (HS : st_ok_pi SEGS VAL E ss_P (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + C0P_D)) m (seg_rom SEGS)))).
{ rewrite HE. apply c0d_seat; [vm_compute; reflexivity | | | ]; rewrite <- HE.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (c0d_rs_ok E m 0x48 (SOff 10 0) NN U9 K S48 (c0d_den0 E 10 _ F10)); lia.
    + apply (c0d_rs_ok E m 0x40 (SOff 32 0) (shadow_addr (r + 280)) U9 K S40 (c0d_den0 E 32 _ F32)); unfold SHADOW_OFF in ESA; lia.
    + apply (c0d_sh_ok E m md 32 (shadow_addr (r + 280)) HJ U32 (c0d_sa_zero m md HJ)); unfold SHADOW_OFF in ESA; lia.
    + apply (c0d_rs_ok E m 0x28 (SOff 20 280) (r + 280) U9 K S28); [| lia | lia | lia].
      exact (c0d_denv E 20 r 280 F20 ltac:(lia)).
    + apply (c0d_rn_ok E m 33 _ U20 ltac:(rewrite HNPL; exact F33) K HREG HLPL ltac:(lia)).
    + apply (c0d_rs_ok E m 0x70 (SOff 34 0) (2 ^ 64 - 1 - r) U9 K S70 (c0d_den0 E 34 _ F34)); lia.
  - unfold c0d_rs, c0d_sh, c0d_rn. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. repeat split; unfold YP09.extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U20, ?U32; unfold SHADOW_OFF in ESA; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [exact (c0d_af9 E U9)|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16; split; [lia|]; split; [exact Hr16 | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U10; rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U33; rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I]. }
assert (SHOK : sh_ok SEGS C0D_Bx [] E (mrestrict (w_H W3) m)) by constructor.
unfold c0d_J in HJ.
paj_run_to_tok RUNTO HS HJ SHOK C0D_span 0x660; [awr_ok_tac |]. c0d_ro K.

psrr_branch_tok RUN BR HS SHOK C0D_span; rewrite branch_ne_U, (c0d_U_atom E 33 _ F33), (c0k_U_off E 10 NN 1 F10 ltac:(lia)) in Hc.
1: { rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK C0D_span 0x660; [awr_ok_tac |]. c0d_ro K.

psrr_branch_tok RUN BR HS SHOK C0D_span;
  rewrite branch_ltu_U, (c0d_U_atom E 34 _ F34), U_SMd, (c0d_U_atom E 10 NN F10), c0d_U_lit in Hc;
  cbn [zmd_raw] in Hc; rewrite !(Z.mod_small NN), (Z.mod_small 56), (Z.mod_small (2 ^ 64 - 1 - r)) in Hc by lia;
  unfold zcanon, M64 in Hc; rewrite (Z.mod_small (NN * 56)) in Hc by lia.
1: { exfalso. apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK C0D_span 0x660; [awr_ok_tac |]. c0d_ro K.

pmkst HS.
c0k_rawreg HS (10%bv : bv 5) Q10. c0k_rawreg HS (11%bv : bv 5) Q11. c0k_rawreg HS (19%bv : bv 5) Q19.
c0k_rawreg HS (23%bv : bv 5) Q23. c0k_rawreg HS (24%bv : bv 5) Q24. c0k_rawreg HS (25%bv : bv 5) Q25.
c0k_rawreg HS (26%bv : bv 5) Q26.
assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite HE, (c0d_ewR regs ex 18 18%bv eq_refl); exact G18).
assert (ER : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr)
  by (intros nn rr Hnn; rewrite HE; apply c0d_ewR; exact Hnn).
rewrite HE in HS.
apply (c0d_P2 _ _ _ b p (c0d_regs_run _ _ _ _ HS eq_refl GR) K HJ HPL HREG).
- rewrite Q10. exact (c0d_rw12_val E NN F10 F20 Hn4).
- rewrite Q11. exact (c0d_rwsh_val E NN F10 F20 F18 Hn4).
- rewrite Q19. exact (c0d_den0 E 10 _ F10).
- rewrite Q23. exact (c0d_rw_val E NN F10 F20 Hn4).
- rewrite Q24, (c0d_den0 E 24 _ (ER 24%nat 24%bv eq_refl)). exact R24G.
- rewrite Q25, (c0d_den0 E 25 _ (ER 25%nat 25%bv eq_refl)). exact R25G.
- rewrite Q26, (c0d_den0 E 26 _ (ER 26%nat 26%bv eq_refl)). exact R26G.
Qed.

End c.

(* ---- the piece: C0_D -> F (refused) or BC (placed) ---- *)
Theorem c0_d : forall POST i, lx_from B MT POST (C0_F B MT i) -> lx_from B MT POST (C0_BC B MT i) ->
  lx_from B MT POST (C0_D B MT i).
Proof.
intros POST i HNF HNBC cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HD.
destruct HD as (pos & r & fab & op & nm & want & bs & HCOM & HNM & HARG & S60 & HW & Hw & S20 & R24 & HRES).
pose proof HCOM as (HBODY & _ & _ & HINV & HFAB & _ & _ & _ & _ & _ & _ & R20 & R21 & R27).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & _).
pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
pose proof HARG as (R23 & R25 & R26 & _).
pose proof HNM as (Hk & Hacc & HBLK & Haf & Hnm4 & Hname & Hcur).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & _ & HF64 & _).
pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as HFeq.
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & _).
pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hnk. fold (c0_nk (lc_pl cx) pos) in Hnk.
assert (Hinr : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
assert (Hinq : In (nm, c0_nk (lc_pl cx) pos + 1) (ablocks B ly3 S3))
  by (rewrite HBLK; apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR Hinr) as (Hr16 & Hr0 & Hr1 & Happr & _).
change (req_size LX_REG) with 288 in Hr1, Happr.
destruct (al_blocks _ _ LAWS _ _ _ _ _ nm _ HAR Hinq) as (_ & _ & Hq1 & _).
pose proof (req_size_pos (c0_nk (lc_pl cx) pos + 1) ltac:(lia)) as [_ Hrq].
pose proof HB as (_ & _ & _ & Hin0 & _).
assert (HGin : lc_n cx = 0 \/ (0 < lc_n cx /\ 4096 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling)).
{ destruct Hin0 as [H0 | (Hn & Hin)]; [left; exact (proj1 H0) | right].
  assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (lc_p cx) (lc_n cx) HAR Hin3) as (_ & Hp0 & Hp1 & _).
  pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. split; [lia|]. split; lia. }
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + C0P_D)) (ms_mem ms3) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hsvc, Hrom, Hfreg, Hfcsr.
  subst. reflexivity. }
assert (GR : c0d_regs cx fp r fab (ms_regs ms3)).
{ split; [exact G2|]. split; [exact G8|]. split; [exact G9|]. split; [exact G3|]. split; [exact G4|].
  split; [exact G18|]. split; [exact G22|]. split; [exact R20|]. split; [exact R21 | exact R27]. }
assert (K0 : c0d_K cx fp W3 ms3 pos r nm (ms_mem ms3)) by exact (c0_kept_refl _ _ _ _ _ _).
assert (HGsp : lsp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= lsp0 cx <= 2 ^ 47 /\
  lsp0 cx - 287 <= lsp1 cx <= lsp0 cx - 256 /\ lsp1 cx mod 32 = 0) by (split; [exact Hsp0al|]; split; [lia|]; split; [lia | exact Hsp1al]).
assert (HGr : r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ In (r, LX_REG) (ablocks B ly3 S3) /\ in_app r 288)
  by (split; [exact Hr16|]; split; [exact Hr0|]; split; [exact Hr1|]; split; [exact Hinr | exact Happr]).
assert (HGF : 4096 <= lF cx fp /\ lF cx fp + 512 <= alloc_ceiling /\ lF cx fp mod 64 = 0 /\
  in_app (lF cx fp) 512 /\ frame_addr ly3 LX_CID fp = lF cx fp)
  by (split; [exact HF0|]; split; [exact HFc|]; split; [exact HF64|]; split; [exact HFapp | exact HFeq]).
assert (HGq : 4096 <= nm /\ nm + (c0_nk (lc_pl cx) pos + 1) <= alloc_ceiling) by lia.
rewrite Hms.
destruct HRES as [(HRF & HREG & R10) | (b & p & HPL & HREG & R10)].
- exact (c0d_R POST i cx fp k acc ly3 S3 W3 ms3 pos r fab op nm want bs HB HFR HMO HNF (conj HCOM (conj HNM HARG))
    S60 HW Hw S20 HGsp HGr HGF HGin HGq (ms_regs ms3) (ms_mem ms3) md3 GR R10 K0 HJ HREG HRF).
- exact (c0d_P1 POST i cx fp k acc ly3 S3 W3 ms3 pos r fab op nm want bs HB HFR HMO HNBC (conj HCOM (conj HNM HARG))
    S60 HW Hw S20 HGsp HGr HGF HGin HGq (ms_regs ms3) (ms_mem ms3) md3 b p GR R10 K0 HJ R24 R25 R26 HPL HREG).
Qed.

End a.
