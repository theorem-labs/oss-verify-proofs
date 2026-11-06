(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its addresses and numbers changed; 434 of its 520 lines of code are new or changed and 180 lines of the source are left out. *)
(* Segment OWE5 of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_owe 5): owe()'s
   RING case (fuzz_codec.c:174-186) with owe_sysex inlined, 0x82488-0x8257c, the E_RANGE tail 0x82730-0x82738, to
   CHK 0x8273c.
     0x82488 the instrumented check of desk + 9, lbu strips; lw a; bgeu a,strips -> E_RANGE;
     0x824a8 lwu b; srli b,15; bnez -> E_RANGE; 0x824b4-0x824c8 the loop's registers;
     0x824cc-0x82510 the led loop (lib/A/Prog/codec_amain_owe5_lib.v o5_loop);
     0x82514 the instrumented check of desk + 8, lbu dev; want[5] = p1, want[6] = p2, want[7] = 0xf7, want_len = 8,
     want[0..2) = 0xf0 0x13 (80(sp1)), want[2] = dev, want[3] = 0, want[4] = a | (b & 1) << 6,
     want_key = 0x30000 | (a & 0xffff), want_display = 0; j CHK. 0x82730 want_rc = -11; 0x82738 s11 = 10.
   The state: k's a and b read-only (atoms 37, 38), want_rc and want[0..8) writable (want[0..8) kept as atoms 43-50
   on the E_RANGE paths), want_len .. want_display writable (0 at the cut), the desk's four bytes (atoms 39-42) on
   atom 23 = s7 = k.desk. After the loop the state is re-seated (lib/Reusable/YI04.v st_ok_after_stretch) with the
   loop's registers t0, t1, a2, a3, a5, a6, a7 as fresh atoms. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkIntr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_lem codec_amain_st codec_amain_owel.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_owe5_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* carry a fact about an atom of an older env to the env Ec of the state (the runs add atoms with ewset, the re-seat
   with havoc, both above the atoms these facts name) *)
Ltac o5_norm := repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia].
Ltac o5_norm_in H := repeat first [rewrite ew_ewset_other in H by lia | rewrite ew_havoc_old in H by lia].
Ltac o5_mv1 Ec H :=
  lazymatch type of H with
  | ew ?Eo ?n = ?v => tryif constr_eq Eo Ec then idtac else
      (let H' := fresh "H" in
       assert (H' : ew Ec n = v) by (let H0 := fresh "H0" in pose proof H as H0; o5_norm_in H0; o5_norm; exact H0);
       clear H; rename H' into H)
  | bv_unsigned (ew ?Eo ?n) = ?v => tryif constr_eq Eo Ec then idtac else
      (let H' := fresh "H" in
       assert (H' : bv_unsigned (ew Ec n) = v)
         by (let H0 := fresh "H0" in pose proof H as H0; o5_norm_in H0; o5_norm; exact H0);
       clear H; rename H' into H)
  end.
Ltac o5_mvW Ec XW kc :=
  lazymatch type of XW with forall j, _ -> ew ?Eo (43 + j) = _ => tryif constr_eq Eo Ec then idtac else
    (let H' := fresh "XW" in
     assert (H' : forall j, (j < 8)%nat -> ew Ec (43 + j) = Z_to_bv 64 (nth j (kz_want kc) 0))
       by (let j := fresh "j" in let Hj := fresh "Hj" in let H0 := fresh "H0" in
           intros j Hj; pose proof (XW j Hj) as H0; o5_norm_in H0; o5_norm; exact H0);
     clear XW; rename H' into XW) end.
Ltac o5_mvall U2 UF X37 X38 X39 X40 X41 X42 E23 E32 XW kc :=
  lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
    o5_mv1 Ec U2; o5_mv1 Ec UF; o5_mv1 Ec X37; o5_mv1 Ec X38; o5_mv1 Ec X39; o5_mv1 Ec X40; o5_mv1 Ec X41;
    o5_mv1 Ec X42; o5_mv1 Ec E23; o5_mv1 Ec E32; o5_mvW Ec XW kc end.

Ltac o5w_rreg HS r Q :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS) end.

(* ================================ the state at OWE5 ================================ *)
Definition o5_k : YP09.region := am_frame_region 200 208 200 200
[YP09.mkChunk 200 (CVal 4 (SOff 37 0)); YP09.mkChunk 204 (CVal 4 (SOff 38 0))].
Definition o5_w : YP09.region := am_frame_region 316 328 316 328
[YP09.mkChunk 316 (CVal 4 (SLit 0));
 YP09.mkChunk 320 (CVal 1 (SOff 43 0)); YP09.mkChunk 321 (CVal 1 (SOff 44 0)); YP09.mkChunk 322 (CVal 1 (SOff 45 0));
 YP09.mkChunk 323 (CVal 1 (SOff 46 0)); YP09.mkChunk 324 (CVal 1 (SOff 47 0)); YP09.mkChunk 325 (CVal 1 (SOff 48 0));
 YP09.mkChunk 326 (CVal 1 (SOff 49 0)); YP09.mkChunk 327 (CVal 1 (SOff 50 0))].
Definition o5_l : YP09.region := am_frame_region 344 360 344 360
[YP09.mkChunk 344 (CVal 8 (SLit 0)); YP09.mkChunk 352 (CVal 4 (SLit 0)); YP09.mkChunk 356 (CVal 4 (SLit 0))].
Definition o5_d : YP09.region := owe_desk_region [SOff 39 0; SOff 40 0; SOff 41 0; SOff 42 0].
Definition o5_rs : smem := [o5_k; o5_w; o5_l; o5_d].
Definition o5_AF : list (nat * afact) :=
[(23%nat, mkAF 0x9d6a0 0x9d6c0 0); (37%nat, mkAF 0 (2 ^ 32 - 1) 0); (38%nat, mkAF 0 (2 ^ 16 - 1) 0)].
Definition o5_ys (kc : kcallZ) (d : desk) : list Z :=
[kz_a kc; kz_b kc; d_dev d; d_strips d; d_chars d; d_counter d] ++ firstn 8 (kz_want kc).

(* ================================ owe()'s RING case ================================ *)
Lemma o5_spec_rng : forall d a b c delta bytes n, 0 <= b -> d_strips d <= a \/ 2 ^ 15 <= b ->
fst (owe_spec 5 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
intros d a b c delta bytes n Hb H. unfold owe_spec. cbv beta iota zeta. cbn [Z.eqb Pos.eqb orb negb].
destruct (Z.leb_spec (d_strips d) a); [reflexivity|].
replace (Z.shiftr b 15 =? 0) with false; [reflexivity|].
symmetry. apply Z.eqb_neq. rewrite Z.shiftr_div_pow2 by lia.
assert (1 <= b / 2 ^ 15) by (apply Z.div_le_lower_bound; lia). lia.
Qed.
Lemma o5_spec_ok : forall d a b c delta bytes n, a < d_strips d -> 0 <= b < 2 ^ 15 ->
owe_spec 5 (Some d) a b c delta bytes n =
(0, ([0xf0; 0x13; u8 (d_dev d); 0; u8 (Z.lor a (bit_or_0 (Z.testbit b 0) 0x40));
      fst (owe_ring b); snd (owe_ring b); 0xf7], KEY 3 a, 0)).
Proof.
intros d a b c delta bytes n Ha Hb. unfold owe_spec. cbv beta iota zeta. cbn [Z.eqb Pos.eqb orb negb].
replace (d_strips d <=? a) with false by (symmetry; apply Z.leb_gt; lia).
replace (Z.shiftr b 15 =? 0) with true
  by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
cbn [orb negb]. destruct (owe_ring b) as [p1 p2]. unfold owe_sx. cbn. reflexivity.
Qed.


(* ================================ helpers of the walk ================================ *)
Lemma o5_DX : forall Ex n v, ew Ex n = Z_to_bv 64 v -> sv_denot Ex (SOff n 0) = Z_to_bv 64 v.
Proof. intros Ex n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma o5_U_zx8 : forall Ex n v, ew Ex n = Z_to_bv 64 v -> 0 <= v < 256 -> U Ex (SExt false 8 (SOff n 0)) = v.
Proof.
intros Ex n v Hv Hr. rewrite U_SExt. cbv iota beta. rewrite (U_atom Ex n v Hv) by lia.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma o5_U_srl15 : forall Ex b, ew Ex 38 = Z_to_bv 64 b -> 0 <= b < 2 ^ 16 ->
U Ex (SAlu ALU_SRL (SOff 38 0) (SLit 15)) = Z.shiftr b 15.
Proof.
intros Ex b Hb Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom Ex 38 b Hb), U_lit by lia.
change (Z.land 15 63) with 15. unfold zcanon, M64. apply Z.mod_small.
rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma o5_lor_ltn : forall n x y, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
intros n x y Hn Hx Hy. split; [apply Z.lor_nonneg; lia|].
assert (E : Z.lor x y = Z.land (Z.lor x y) (Z.ones n)).
{ rewrite Z.land_lor_distr_l, !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
rewrite E, Z.land_ones by lia. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn).
pose proof (Z.mod_pos_bound (Z.lor x y) (2 ^ n) ltac:(lia)). lia.
Qed.
(* andi of b << 6 with 64: bit 0 of b in bit 6 (lib/Prog/codec_main_owe5.v:210-222 of the plain walk, land_shl6) *)
Lemma o5_land_shl6 : forall b, 0 <= b -> Z.land (Z.shiftl b 6) 64 = bit_or_0 (Z.testbit b 0) 64.
Proof.
intros b Hb. apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec. change 64 with (2 ^ 6). rewrite Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec 6 n) as [<- | Hne].
- rewrite andb_true_r. rewrite Z.shiftl_spec by lia. replace (6 - 6) with 0 by lia.
  destruct (Z.testbit b 0); cbn [bit_or_0]; [rewrite Z.pow2_bits_eqb by lia; reflexivity | rewrite Z.bits_0; reflexivity].
- rewrite andb_false_r. destruct (Z.testbit b 0); cbn [bit_or_0];
    [rewrite Z.pow2_bits_eqb by lia; symmetry; apply Z.eqb_neq; exact Hne | rewrite Z.bits_0; reflexivity].
Qed.
(* 0x8252c andi a4,a4,64; 0x82550 or a1,a4,a1: want[4] *)
Lemma o5_U_x : forall E a b, ew E 37 = Z_to_bv 64 a -> ew E 38 = Z_to_bv 64 b -> 0 <= a < 64 -> 0 <= b < 2 ^ 16 ->
U E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SLL (SOff 38 0) (SLit 6)) (SLit 64)) (SExt true 32 (SOff 37 0)))
= Z.lor a (bit_or_0 (Z.testbit b 0) 64).
Proof.
intros E a b H37 H38 Ha Hb.
assert (Us : U E (SExt true 32 (SOff 37 0)) = a).
{ rewrite (owe_U_sx32 E 37 a H37) by lia. destruct (Z.ltb_spec a (2 ^ 31)); lia. }
assert (Ul : U E (SAlu ALU_SLL (SOff 38 0) (SLit 6)) = Z.shiftl b 6).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 38 b H38), U_lit by lia. change (Z.land 6 63) with 6.
  unfold zcanon, M64. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia. lia. }
assert (Bx : 0 <= bit_or_0 (Z.testbit b 0) 64 < 128) by (destruct (Z.testbit b 0); cbn; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite Us. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ul, U_lit by lia.
rewrite o5_land_shl6 by lia.
unfold zcanon, M64. rewrite (Z.mod_small (bit_or_0 _ 64)) by lia.
pose proof (o5_lor_ltn 7 (bit_or_0 (Z.testbit b 0) 64) a ltac:(lia) ltac:(change (2 ^ 7) with 128; exact Bx)
  ltac:(change (2 ^ 7) with 128; lia)) as L. change (2 ^ 7) with 128 in L.
rewrite Z.mod_small by lia. apply Z.lor_comm.
Qed.
(* 0x8254c-0x8255c: want_key = (a & 0xffff) | 0x30000 *)
Lemma o5_U_key : forall E a, ew E 37 = Z_to_bv 64 a -> 0 <= a < 2 ^ 16 ->
U E (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 48)) (SLit 48)) (SLit 196608))
= KEY 3 a.
Proof.
intros E a H37 Ha.
assert (Us : U E (SExt true 32 (SOff 37 0)) = a).
{ rewrite (owe_U_sx32 E 37 a H37) by lia. destruct (Z.ltb_spec a (2 ^ 31)); lia. }
assert (Ul : U E (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 48)) (SLit 48)) = a).
{ rewrite !U_SAlu. cbn [zalu_raw]. rewrite Us, !U_lit by lia. change (Z.land 48 63) with 48.
  rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
  rewrite (Z.mod_small (a * 2 ^ 48)) by (change (2 ^ 48) with 281474976710656; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by (change (2 ^ 48) with 281474976710656; lia).
  apply Z.mod_small. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ul, U_lit by lia.
unfold KEY. change (3 * 65536) with 196608. change 0xffff with (Z.ones 16).
rewrite Z.land_ones by lia. rewrite (Z.mod_small a) by lia.
pose proof (o5_lor_ltn 18 a 196608 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as L.
unfold zcanon, M64. rewrite Z.mod_small by (cbn in L; lia). apply Z.lor_comm.
Qed.
Definition o5_bs (kc : kcallZ) (d : desk) : list Z :=
[0xf0; 0x13; u8 (d_dev d); 0; u8 (Z.lor (kz_a kc) (bit_or_0 (Z.testbit (kz_b kc) 0) 0x40));
 fst (owe_ring (kz_b kc)); snd (owe_ring (kz_b kc)); 0xf7].

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a re-seat over a memory whose restricted bytes are the old ones keeps every region *)
Lemma o5_kept_eq : forall E H (m m' : word -> option byte) r,
(forall x, mrestrict H m' x = mrestrict H m x) -> region_kept tfibsegs E (mrestrict H m) (mrestrict H m') r.
Proof.
intros E H m m' r Hm. split.
- intros a _. unfold mbyte. rewrite Hm. reflexivity.
- intros a _ Hw. apply (cw_writable_kept H m m' a); [|exact Hw].
  intros Hp. eapply apresent_grows; [|exact Hp]. intros x Hx. rewrite Hm. exact Hx.
Qed.
(* the shadow entries of atoms below 34 hold in an env that agrees below 34 and a memory with the same bytes *)
Lemma o5_sh_move : forall E E' (m m' : word -> option byte) SH,
sh_ok tfibsegs CW_Bx SH E m -> (forall n, (n < 34)%nat -> ew E' n = ew E n) ->
Forall (fun e => (she_m e < 34)%nat) SH -> (forall x, m' x = m x) -> sh_ok tfibsegs CW_Bx SH E' m'.
Proof.
intros E E' m m' SH H HE HS Hm. unfold sh_ok in *.
assert (UE : forall n o, (n < 34)%nat -> U E' (SOff n o) = U E (SOff n o)) by (intros n o Hn; rewrite !U_SOff, HE by lia; reflexivity).
rewrite Forall_forall in H, HS |- *. intros e He. specialize (H e He). specialize (HS e He).
destruct H as [Hra Hap]. unfold CW_Bx in *. split.
- rewrite (UE 32%nat 0), (UE (she_m e) 0) by lia. intros x Hx. destruct (Hra x Hx) as (s0 & Hs & Hok).
  exists s0. split; [|exact Hok]. unfold rd_of, mbyte in *. rewrite Hm. exact Hs.
- intros a Ha. rewrite (UE 32%nat 0) by lia. apply Hap. rewrite <- (UE (she_m e) 0) by lia. exact Ha.
Qed.
End k.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.

Theorem seg_owe5_holds : seg_owe B MT K XM_LIB 5.
Proof using TL LAWS GM IV ROB.
unfold seg_owe. intros g pos sp1 ops W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & _ & c & kc & od & Hcur & Hkat & Hrec & Hkind & Hod & Hrc & Hw0 & Hwl0 & Hwk0 & Hwd0 & R23).
destruct od as [d|]; [| exfalso; destruct (Hod eq_refl) as [X | [X | X]]; lia].
pose proof Hrec as (_ & Hpd & Hrdr & _ & _).
pose proof Hrdr as (Ra & Rb & _ & _ & _ & _ & _ & R5 & _ & _). rewrite Hkind in R5. specialize (R5 eq_refl).
destruct (pd_range_A _ _ d Hpd) as (Hpv & Hdv & Rdev & Rstr & Rch & Rcnt).
unfold CM_SPEC_C24, CM_SPEC_PC in Hdv.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hkat as (HK & HW).
destruct HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbef & Gout & Vwrc & Gwant & Vwl & Vwk & Vwd).
destruct HW as (Wkind & Wp & Wdesk & Wa & Wb & Wc & Wdelta & Wn & Wrc & Wwrc & Wwl & Wwk & Wwd & Lbytes & Lbef & Lout & Lwant).
pose proof HC as (Hpre & _ & R2 & _).
assert (HRO : arodata_ok B (aview tfibsegs (w_H W2) mem2)) by exact (arodata_ok_at B MT K XM_LIB g _ _ _ _ _ _ _ Hpre HJ).
set (dv := kz_desk kc) in *.
set (ys := o5_ys kc d).
set (E := am_env g pos c regs2 ys).
assert (DX : forall n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (X37 : ew E 37 = Z_to_bv 64 (kz_a kc)) by exact (am_ew_y g pos c regs2 ys 0).
assert (X38 : ew E 38 = Z_to_bv 64 (kz_b kc)) by exact (am_ew_y g pos c regs2 ys 1).
assert (X39 : ew E 39 = Z_to_bv 64 (d_dev d)) by exact (am_ew_y g pos c regs2 ys 2).
assert (X40 : ew E 40 = Z_to_bv 64 (d_strips d)) by exact (am_ew_y g pos c regs2 ys 3).
assert (X41 : ew E 41 = Z_to_bv 64 (d_chars d)) by exact (am_ew_y g pos c regs2 ys 4).
assert (X42 : ew E 42 = Z_to_bv 64 (d_counter d)) by exact (am_ew_y g pos c regs2 ys 5).
assert (XW : forall j, (j < 8)%nat -> ew E (43 + j) = Z_to_bv 64 (nth j (kz_want kc) 0)).
{ intros j Hj. change (43 + j)%nat with (AM_X0 + (6 + j))%nat.
  transitivity (Z_to_bv 64 (nth (6 + j) ys 0)); [exact (am_ew_y g pos c regs2 ys (6 + j)) |].
  f_equal. unfold ys, o5_ys. rewrite app_nth2 by (cbn; lia). cbn [length].
  replace (6 + j - 6)%nat with j by lia. rewrite nth_firstn. replace (j <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  reflexivity. }
assert (QW : forall j, (j < 8)%nat ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 320 + Z.of_nat j) 1 (nth j (kz_want kc) 0) /\
  0 <= nth j (kz_want kc) 0 < 256).
{ intros j Hj. destruct (Gwant j ltac:(lia)) as [G Q]. split; [|exact Q].
  replace (FA g pos + 320 + Z.of_nat j) with (FA g pos + 176 + 144 + Z.of_nat j) by lia. exact G. }
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (am_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
assert (E23 : ew E 23 = Z_to_bv 64 dv).
{ subst E. rewrite (am_ew_reg g pos c regs2 ys 23 23%bv eq_refl), R23. reflexivity. }
assert (U23 : bv_unsigned (ew E 23) = dv) by (rewrite E23; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (am_ew_SB g pos c regs2 ys).
(* the entry state *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o5_rs).
{ unfold o5_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  - unfold o5_k. apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
    [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 200 4 (SOff 37 0) (kz_a kc)); [exact (DX 37%nat _ X37) | zside | zside |].
      replace (FA g pos + 200) with (FA g pos + 176 + 24) by lia. exact Va.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 204 4 (SOff 38 0) (kz_b kc)); [exact (DX 38%nat _ X38) | zside | zside |].
      replace (FA g pos + 204) with (FA g pos + 176 + 28) by lia. exact Vb.
  - unfold o5_w. apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
    [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ].
    apply Forall_cons.
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 316 4 (SLit 0) 0); [reflexivity | zside | zside |].
      replace (FA g pos + 316) with (FA g pos + 176 + 140) by lia. rewrite <- Hw0. exact Vwrc. }
    assert (CW : forall j, (j < 8)%nat ->
      YP09.chunk_ok tfibsegs E (mrestrict (w_H W2) mem2) (FA g pos)
        (YP09.mkChunk (320 + Z.of_nat j) (CVal 1 (SOff (43 + j) 0)))).
    { intros j Hj. destruct (QW j Hj) as [G Q].
      apply (chunk_ok_val tfibsegs E _ (FA g pos) (320 + Z.of_nat j) 1 (SOff (43 + j) 0) (nth j (kz_want kc) 0));
      [exact (DX _ _ (XW j Hj)) | cbn; lia | zside |].
      replace (FA g pos + (320 + Z.of_nat j)) with (FA g pos + 320 + Z.of_nat j) by lia. exact G. }
    repeat apply Forall_cons; try apply Forall_nil;
    [ apply (CW 0%nat) | apply (CW 1%nat) | apply (CW 2%nat) | apply (CW 3%nat) | apply (CW 4%nat) | apply (CW 5%nat)
    | apply (CW 6%nat) | apply (CW 7%nat) ]; lia.
  - unfold o5_l. apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
    [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 344 8 (SLit 0) 0); [reflexivity | zside | zside |].
      replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia. rewrite <- Hwl0. exact Vwl.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 352 4 (SLit 0) 0); [reflexivity | zside | zside |].
      replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia. rewrite <- Hwk0. exact Vwk.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 356 4 (SLit 0) 0); [reflexivity | zside | zside |].
      replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia. rewrite <- Hwd0. exact Vwd.
  - unfold o5_d. apply (owe_desk_region_ok B TL E W2 mem2 (kz_p kc) dv d); [exact HRO | exact Hpd | exact U23 |].
    intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth desk_bytesZ];
    [exact (DX _ _ X39) | exact (DX _ _ X40) | exact (DX _ _ X41) | exact (DX _ _ X42) | lia]. }
assert (Hpd2 : pairwise_disjoint E o5_rs).
{ unfold o5_rs, o5_k, o5_w, o5_l, o5_d, owe_desk_region, am_frame_region. cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF, U23.
  pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos dv 12 0 448 (proj1 HJ)
    ltac:(rewrite Hfr; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(change (fs_frame_bytes 3) with 512; lia))
    as Hap. rewrite EFA in Hap.
  repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r am_regs) o5_rs).
{ unfold o5_rs. repeat apply Forall_cons; try apply Forall_nil.
  1-3: apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
       [exact HJ | exact Hfr | exact HC | lia | lia].
  apply (owe_desk_apart_base E _ dv sp1 U23 ltac:(lia) U2). lia. }
assert (HAF : atoms_ok E o5_AF).
{ unfold o5_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E23, X37, X38. rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia. }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 5) ys o5_rs o5_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd2 Hap HAF) as HS.
fold E in HS. change (owe_pc 5) with 0x82488 in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_desk_SH; owe_SHk] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p kc) dv d GM IV (proj1 HJ) Hpd E23 E32).
  - exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 8 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HAE : env_agree 37 (am_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
pose proof HJ as HJR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (owe_U_sx32 E 37 (kz_a kc) X37 ltac:(lia)) as Ua.
assert (OK : owe_kZ kc (Some d) = owe_spec 5 (Some d) (kz_a kc) (kz_b kc) (kz_c kc) (kz_delta kc) (kz_bytes kc) (kz_n kc))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
unfold cfg_at. change (w64 0x82488) with (Z_to_bv 64 0x82488).
(* 0x82488-0x824a4: desk + 9, a; bgeu a,strips *)
assert (QA : forall j, (j < 8)%nat -> 0 <= nth j (kz_want kc) 0 < 256) by (intros j Hj; apply (QW j Hj)).
pose proof (QA 0%nat ltac:(lia)) as Q0. pose proof (QA 1%nat ltac:(lia)) as Q1. pose proof (QA 2%nat ltac:(lia)) as Q2.
pose proof (QA 3%nat ltac:(lia)) as Q3. pose proof (QA 4%nat ltac:(lia)) as Q4. pose proof (QA 5%nat ltac:(lia)) as Q5.
pose proof (QA 6%nat ltac:(lia)) as Q6. pose proof (QA 7%nat ltac:(lia)) as Q7.
cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
o5_mvall U2 UF X37 X38 X39 X40 X41 X42 E23 E32 XW kc.
cw_branch Hb1.
all: rewrite branch_geu_U, (owe_U_sx32 _ 37 (kz_a kc) X37 ltac:(lia)), (o5_U_zx8 _ 40 (d_strips d) X40 Rstr) in Hb1.
- (* strips <= a: the E_RANGE tail, to CHK *)
  apply negb_true_iff, Z.ltb_ge in Hb1.
  assert (Herr : d_strips d <= kz_a kc) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  all: idtac.
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x8273c. cw_keep ltac:(owe_kwr U2 UF).
  o5_mvall U2 UF X37 X38 X39 X40 X41 X42 E23 E32 XW kc.
  lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
    assert (HAE2 : env_agree 37 (am_env g pos c regs2 ys) Ec) by env_agree_chain HAE;
    assert (DXc : forall n v, ew Ec n = Z_to_bv 64 v -> sv_denot Ec (SOff n 0) = Z_to_bv 64 v)
      by (intros n v Hv; exact (o5_DX Ec n v Hv)) end.
  owe_fields HS UF Hrw Hrl.
  owe_fld Hrw UF 320 1%N V320. owe_fld Hrw UF 321 1%N V321. owe_fld Hrw UF 322 1%N V322. owe_fld Hrw UF 323 1%N V323.
  owe_fld Hrw UF 324 1%N V324. owe_fld Hrw UF 325 1%N V325. owe_fld Hrw UF 326 1%N V326. owe_fld Hrw UF 327 1%N V327.
  pose proof (XW 0%nat ltac:(lia)) as XW0. pose proof (XW 1%nat ltac:(lia)) as XW1. pose proof (XW 2%nat ltac:(lia)) as XW2.
  pose proof (XW 3%nat ltac:(lia)) as XW3. pose proof (XW 4%nat ltac:(lia)) as XW4. pose proof (XW 5%nat ltac:(lia)) as XW5.
  pose proof (XW 6%nat ltac:(lia)) as XW6. pose proof (XW 7%nat ltac:(lia)) as XW7.
  cbn [Nat.add] in XW0, XW1, XW2, XW3, XW4, XW5, XW6, XW7.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  lazymatch type of HS with st_ok _ ?Ec _ _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 8
    m3 r3 md3 Ec _ (-11) (firstn 8 (kz_want kc)) 0 0 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE2 HS) end end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | rewrite length_firstn, Lwant; reflexivity | rewrite length_firstn, Lwant; cbn; lia
  | exact KE | | | | | | lia | lia | lia | lia | ].
  + apply (owe_vm _ _ 4 _ _ V316). vm_compute. reflexivity.
  + intros j Hj. rewrite length_firstn, Lwant in Hj. cbn in Hj.
    rewrite nth_firstn, (proj2 (Nat.ltb_lt j 8) ltac:(lia)).
    split; [| apply (QW j); lia].
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
    [ owe_byte V320 DXc XW0 | owe_byte V321 DXc XW1 | owe_byte V322 DXc XW2 | owe_byte V323 DXc XW3
    | owe_byte V324 DXc XW4 | owe_byte V325 DXc XW5 | owe_byte V326 DXc XW6 | owe_byte V327 DXc XW7 | lia ].
  + apply (owe_vm _ _ 8 _ _ V344). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V352). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V356). vm_compute. reflexivity.
  + apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply o5_spec_rng; lia.

- (* a < strips *)
  apply negb_false_iff, Z.ltb_lt in Hb1.
  assert (Ha : kz_a kc < d_strips d) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  (* 0x824a8-0x824b0: lwu b, srli 15, bnez *)
  cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
  o5_mvall U2 UF X37 X38 X39 X40 X41 X42 E23 E32 XW kc.
  cw_branch Hb2.
  all: rewrite branch_ne_U, (o5_U_srl15 _ (kz_b kc) X38 ltac:(lia)), U_lit in Hb2 by lia.
  + (* b >= 2^15: the E_RANGE tail *)
    apply negb_true_iff, Z.eqb_neq in Hb2.
    assert (Herr : 2 ^ 15 <= kz_b kc).
    { destruct (Z.ltb_spec (kz_b kc) (2 ^ 15)) as [Hl|Hl]; [|exact Hl]. exfalso. apply Hb2.
      rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x8273c. cw_keep ltac:(owe_kwr U2 UF).
    o5_mvall U2 UF X37 X38 X39 X40 X41 X42 E23 E32 XW kc.
    lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
      assert (HAE2 : env_agree 37 (am_env g pos c regs2 ys) Ec) by env_agree_chain HAE;
      assert (DXc : forall n v, ew Ec n = Z_to_bv 64 v -> sv_denot Ec (SOff n 0) = Z_to_bv 64 v)
        by (intros n v Hv; exact (o5_DX Ec n v Hv)) end.
    owe_fields HS UF Hrw Hrl.
    owe_fld Hrw UF 320 1%N V320. owe_fld Hrw UF 321 1%N V321. owe_fld Hrw UF 322 1%N V322. owe_fld Hrw UF 323 1%N V323.
    owe_fld Hrw UF 324 1%N V324. owe_fld Hrw UF 325 1%N V325. owe_fld Hrw UF 326 1%N V326. owe_fld Hrw UF 327 1%N V327.
    pose proof (XW 0%nat ltac:(lia)) as XW0. pose proof (XW 1%nat ltac:(lia)) as XW1. pose proof (XW 2%nat ltac:(lia)) as XW2.
    pose proof (XW 3%nat ltac:(lia)) as XW3. pose proof (XW 4%nat ltac:(lia)) as XW4. pose proof (XW 5%nat ltac:(lia)) as XW5.
    pose proof (XW 6%nat ltac:(lia)) as XW6. pose proof (XW 7%nat ltac:(lia)) as XW7.
    cbn [Nat.add] in XW0, XW1, XW2, XW3, XW4, XW5, XW6, XW7.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    lazymatch type of HS with st_ok _ ?Ec _ _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 8
      m3 r3 md3 Ec _ (-11) (firstn 8 (kz_want kc)) 0 0 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE2 HS) end end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | rewrite length_firstn, Lwant; reflexivity | rewrite length_firstn, Lwant; cbn; lia
    | exact KE | | | | | | lia | lia | lia | lia | ].
    * apply (owe_vm _ _ 4 _ _ V316). vm_compute. reflexivity.
    * intros j Hj. rewrite length_firstn, Lwant in Hj. cbn in Hj.
      rewrite nth_firstn, (proj2 (Nat.ltb_lt j 8) ltac:(lia)).
      split; [| apply (QW j); lia].
      destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [ owe_byte V320 DXc XW0 | owe_byte V321 DXc XW1 | owe_byte V322 DXc XW2 | owe_byte V323 DXc XW3
      | owe_byte V324 DXc XW4 | owe_byte V325 DXc XW5 | owe_byte V326 DXc XW6 | owe_byte V327 DXc XW7 | lia ].
    * apply (owe_vm _ _ 8 _ _ V344). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V352). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V356). vm_compute. reflexivity.
    * apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply o5_spec_rng; lia.

  + (* b < 2^15: to the led loop *)
    apply negb_false_iff, Z.eqb_eq in Hb2.
    assert (Hb15 : kz_b kc < 2 ^ 15).
    { rewrite Z.shiftr_div_pow2 in Hb2 by lia. destruct (Z.ltb_spec (kz_b kc) (2 ^ 15)) as [Hl|Hl]; [exact Hl|].
      assert (1 <= kz_b kc / 2 ^ 15) by (apply Z.div_le_lower_bound; lia). lia. }
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x824cc. cw_keep ltac:(owe_kwr U2 UF).
    o5_mvall U2 UF X37 X38 X39 X40 X41 X42 E23 E32 XW kc.
    lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
      assert (HAEL : env_agree 37 (am_env g pos c regs2 ys) Ec) by env_agree_chain HAE end.
    o5w_rreg HS (10%bv : bv 5) L10. o5w_rreg HS (12%bv : bv 5) L12. o5w_rreg HS (13%bv : bv 5) L13. o5w_rreg HS (15%bv : bv 5) L15.
    o5w_rreg HS (16%bv : bv 5) L16. o5w_rreg HS (7%bv : bv 5) L7. o5w_rreg HS (28%bv : bv 5) L28.
    pose proof HS as HSL.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
    lazymatch goal with HS : st_ok _ _ ?ssv _ |- _ => let p := eval vm_compute in (ss_pc ssv) in change (ss_pc ssv) with p end.
    (* 0x824cc-0x82510: the led loop *)
    eapply (o5_loop B LAWS 14 0) with (b := kz_b kc); [lia | lia | lia | exact HJR | | | | | | | | ].
    * rewrite L10. exact (o5_DX _ _ _ X38).
    * rewrite L13. cbn [sv_denot]. reflexivity.
    * apply (o5_reg _ _ _ _ L12). rewrite (o5_U_srl15 _ _ X38) by lia. rewrite Hb2. reflexivity.
    * rewrite L15. reflexivity.
    * rewrite L16. reflexivity.
    * rewrite L7. reflexivity.
    * rewrite L28. reflexivity.
    * intros regs' mem' md' HJ' Hkeep V13 V12 Mm.
      (* the state re-seated at 0x82514: t0 t1 a2 a3 a5 a6 a7 fresh atoms *)
      lazymatch type of HSL with st_ok _ ?Ec ?ss (restrict ?Hh ?ms) =>
        let K := eval vm_compute in (run_K 0 CW_Bx [] ss) in
        pose proof (st_ok_after_stretch tfibsegs K Ec ss (restrict Hh ms) regs' (mrestrict Hh mem') (ss_mem ss) 0x82514
          O5_CLOB HSL eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) (submem_refl _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          (fun r Hr => Hkeep r Hr)
          ltac:(apply Forall_forall; intros r _; exact (o5_kept_eq Ec Hh (ms_mem ms) mem' r Mm))) as HS2;
        assert (SHOK2 : sh_ok tfibsegs CW_Bx [owe_desk_SH; owe_SHk] (havoc Ec K (map (getr regs') O5_CLOB))
          (mrestrict Hh mem'))
        by (apply (o5_sh_move Ec _ (mrestrict Hh (ms_mem ms)) (mrestrict Hh mem') _ SHOK);
            [ intros n0 Hn0; apply ew_havoc_old; lia
            | repeat apply Forall_cons; try apply Forall_nil; cbn; lia
            | exact Mm ]);
        assert (XP1 : ew (havoc Ec K (map (getr regs') O5_CLOB)) (K + 3) = Z_to_bv 64 (fst (owe_ring (kz_b kc))))
          by (rewrite (ew_havoc_new Ec K _ 3 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia); exact V13);
        assert (XP2 : ew (havoc Ec K (map (getr regs') O5_CLOB)) (K + 2) = Z_to_bv 64 (snd (owe_ring (kz_b kc))))
          by (rewrite (ew_havoc_new Ec K _ 2 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia); exact V12);
        cbn [Nat.add] in XP1, XP2
      end.
      rewrite <- restrict_mkst_fx in HS2.
      assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 8 a ->
        aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) mem2 a).
      { intros a0 Ha0 Hz. rewrite <- (KE a0 Ha0 Hz). unfold aview, mbyte. rewrite Mm. reflexivity. }
      clear HS SHOK KE HJR. rename HS2 into HS. rename SHOK2 into SHOK. rename KE2 into KE. rename HJ' into HJR.
      lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
        assert (HAE3 : env_agree 37 (am_env g pos c regs2 ys) Ec) by env_agree_chain HAEL end.
      o5_mvall U2 UF X37 X38 X39 X40 X41 X42 E23 E32 XW kc.
      (* 0x82514-0x8257c: desk + 8, the command, to CHK *)
      cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x8273c. cw_keep ltac:(owe_kwr U2 UF).
      o5_mvall U2 UF X37 X38 X39 X40 X41 X42 E23 E32 XW kc.
      lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
        o5_mv1 Ec XP1; o5_mv1 Ec XP2;
        assert (HAE4 : env_agree 37 (am_env g pos c regs2 ys) Ec) by env_agree_chain HAE3 end.
      assert (Hst24 : d_strips d <= 24)
        by (destruct Hpd as [(_ & _ & H0) | [(_ & _ & H0) | (_ & _ & H0)]];
            [discriminate H0 | injection H0 as ->; cbn; lia | injection H0 as ->; cbn; lia]).
      destruct (o5_acc_range (kz_b kc) 14 ltac:(lia)) as (P1 & P2). rewrite o5_acc_14 in P1, P2.
      owe_fields HS UF Hrw Hrl.
      owe_fld Hrw UF 320 2%N V320. owe_fld Hrw UF 322 1%N V322. owe_fld Hrw UF 323 1%N V323. owe_fld Hrw UF 324 1%N V324.
      owe_fld Hrw UF 325 1%N V325. owe_fld Hrw UF 326 1%N V326. owe_fld Hrw UF 327 1%N V327.
      destruct (owe_split2 _ _ _ 5104 V320 ltac:(vm_compute; reflexivity) ltac:(lia)) as (B0 & B1).
      assert (KR : 0 <= KEY 3 (kz_a kc) < 2 ^ 32).
      { unfold KEY. change (3 * 65536) with 196608. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
        pose proof (Z.mod_pos_bound (kz_a kc) (2 ^ 16) ltac:(lia)).
        pose proof (o5_lor_ltn 18 196608 (kz_a kc mod 2 ^ 16) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as L.
        cbn in L. lia. }
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
      lazymatch type of HS with st_ok _ ?Ec _ _ =>
      apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 8
        m3 r3 md3 Ec _ 0 (map u8 (o5_bs kc d)) 8 (KEY 3 (kz_a kc)) 0
        HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE4 HS) end end;
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
      | exact KE | | | | | | lia | lia | lia | lia | ].
      -- apply (owe_vm _ _ 4 _ _ V316). vm_compute. reflexivity.
      -- intros j Hj. cbn [length map o5_bs] in Hj.
         destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; cbn [nth map o5_bs]; try (split; [| apply owe_u8_range]).
         ++ replace (FA g pos + 320 + Z.of_nat 0) with (FA g pos + 320) by lia.
            apply (owe_vm _ _ 1 _ _ B0). vm_compute. reflexivity.
         ++ replace (FA g pos + 320 + Z.of_nat 1) with (FA g pos + 320 + 1) by lia.
            apply (owe_vm _ _ 1 _ _ B1). vm_compute. reflexivity.
         ++ replace (FA g pos + 320 + Z.of_nat 2) with (FA g pos + 322) by lia.
            apply (owe_vm _ _ 1 _ _ V322). change (bv_unsigned (sv_denot ?E ?e)) with (U E e).
            rewrite (o5_U_zx8 _ 39 (d_dev d) X39 Rdev). unfold u8.
            change (2 ^ (8 * Z.of_N 1)) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256.
            rewrite !Z.mod_mod by lia. reflexivity.
         ++ replace (FA g pos + 320 + Z.of_nat 3) with (FA g pos + 323) by lia.
            apply (owe_vm _ _ 1 _ _ V323). vm_compute. reflexivity.
         ++ replace (FA g pos + 320 + Z.of_nat 4) with (FA g pos + 324) by lia.
            apply (owe_vm _ _ 1 _ _ V324). change (bv_unsigned (sv_denot ?E ?e)) with (U E e).
            rewrite (o5_U_x _ (kz_a kc) (kz_b kc) X37 X38) by lia. unfold u8.
            change (2 ^ (8 * Z.of_N 1)) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256.
            rewrite !Z.mod_mod by lia. reflexivity.
         ++ replace (FA g pos + 320 + Z.of_nat 5) with (FA g pos + 325) by lia.
            apply (owe_vm _ _ 1 _ _ V325). change (bv_unsigned (sv_denot ?E ?e)) with (U E e).
            rewrite (U_atom _ 54 _ XP1) by lia. unfold u8.
            change (2 ^ (8 * Z.of_N 1)) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256.
            rewrite !Z.mod_mod by lia. rewrite Z.mod_small by lia. reflexivity.
         ++ replace (FA g pos + 320 + Z.of_nat 6) with (FA g pos + 326) by lia.
            apply (owe_vm _ _ 1 _ _ V326). change (bv_unsigned (sv_denot ?E ?e)) with (U E e).
            rewrite (U_atom _ 53 _ XP2) by lia. unfold u8.
            change (2 ^ (8 * Z.of_N 1)) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256.
            rewrite !Z.mod_mod by lia. rewrite Z.mod_small by lia. reflexivity.
         ++ replace (FA g pos + 320 + Z.of_nat 7) with (FA g pos + 327) by lia.
            apply (owe_vm _ _ 1 _ _ V327). vm_compute. reflexivity.
         ++ lia.
      -- apply (owe_vm _ _ 8 _ _ V344). vm_compute. reflexivity.
      -- apply (owe_vm _ _ 4 _ _ V352). change (bv_unsigned (sv_denot ?E ?e)) with (U E e).
         rewrite (o5_U_key _ (kz_a kc) X37) by lia.
         change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
         rewrite Z.mod_mod by lia. reflexivity.
      -- apply (owe_vm _ _ 4 _ _ V356). vm_compute. reflexivity.
      -- apply (owe_want_ok_succ kc (Some d) _ (o5_bs kc d) (KEY 3 (kz_a kc)) 0).
         { rewrite OK. unfold o5_bs. apply o5_spec_ok; lia. }
         rewrite <- (length_map u8 (o5_bs kc d)), firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.
End b.
End a.
