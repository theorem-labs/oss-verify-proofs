(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 246 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, which holds the same loaded bytes). Proves no
   function (kind: segment lemma): the piece W14-asked of LLVMFuzzerTestOneInput's segment M02, whose statement is
   lib/A/RtPgSeg.v's rs_piece_W14_asked_stmt; nothing here restates a cut.

   THE ASKED SET-UP (rs_cut_A at A 0x82ca8 -> rs_cut_DEC at DEC 0x82d14, turn 0), fuzz_rate.c:262:
     0x82ca8 ld a0,0x40(s1) (b5); ld a1,0x38(s1) (b6 << 8); or a1,a1,a0; ld a0,0x20(s1) (b3); ld a2,0x48(s1)
             (b4 << 8); or a2,a2,a0; addi a0,s6,0x190 (s6 = F); addi a3,zero,4; sb a3,0x32(s4); sb a3,0x34(s4)
             (asked[0]'s and asked[1]'s granules := 4); addi s6,s6,0x1a0; slli a1,a1,16; or a1,a2,a1 (other);
             addi a3,zero,1; slli a2,s10,62 (s10 = the flags byte);
     0x82ce4 bne s8,a3 -> 0x82cf0 (s8 = rc); lw a3,0(s5) (the hz cell); j 0x82cf8; 0x82cf0 a3 := 48000;
     0x82cf8 srli s5,a2,63 (the role, bit 1 of the flags byte); sw a3,0(a0) (asked[0]); sw a1,0(s6) (asked[1]);
             auipc/addi s11 = 0x21520 (closed_list); addi s3,zero,1; ld s10,0x120(s1) (mask).
   No instrumented check lies in it, so it is one run of the plain engine (lib/A/RtPgW14Base.v w14_run) from an
   entry state with six regions: the real frame at s1 (the cells R+0x20/0x38/0x40/0x48 and R+0x120, read only, their
   values the header cells of rs_Hc as env atoms 32 .. 36), the hz cell at s5 (env atom 37, rs_hz_at), asked[0] and
   asked[1] at s6 = F (write windows, write right RtPgSteps.rts_awr_ok_fobj) and the two shadow bytes 0x32 / 0x34 at
   s4 (write right rts_awr_ok_fsh). s8 is the literal rc: the parse's answer is rc = 1, 0 or -1 (Rate.answer_ok,
   w14_rc3), and the engine decides `bne s8,a3` itself in each case.
   - asked[0] = rc = 1 ? hz : 48000: the run leaves CVal 4 (sext32 of the hz atom), whose low 4 bytes are hz's
     (w14_sext32_low), or CVal 4 48000;
   - asked[1] = other: the run leaves CVal 4 of the `or` tree of the four cells, whose value is rs_other (w14_U_other,
     w14_other_val: b3 + 256 b4 + 65536 (b5 + 256 b6) < 2^32 by rt_hdr_ok);
   - s5 = bit 1 of the flags byte: checked over the 256 byte values (w14_bit1);
   - the frame's shadow goes from rs_PZ to rs_PB (granules 50 and 52 := 4, w14_fsh_PB); every other byte the DEC cut
     names is outside the run's four write windows (w14_wr), so it is kept.

   SECTION HYPOTHESIS of rt_w14_asked_A (Section m): MTL : ameter_laws MT. The frame's laws are the kernel theorem
   YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg RtPgMem RtPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgCheck RtPgM02Base RtPgW14Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================= the run's regions ======================================= *)
(* the real frame's five cells the set-up reads, as env atoms 32 .. 36 *)
Definition w14_rframe : YP09.region := m2_frame 0x20 0x128 0 0
  [YP09.mkChunk 0x20 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x38 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0x40 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x48 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0x120 (CVal 8 (SOff 36 0))].
(* the hz cell at s5 = F + 0x180, its 4 bytes the env atom 37 *)
Definition w14_rhz : YP09.region := m2_hzcell (SOff 37 0).
(* a 4-byte object of the frame for locals at s6 = F + o, writable *)
Definition w14_robj (o : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 22%nat) o (o + 4) o (o + 4) cs.
(* one shadow byte of the frame at s4 = shadow_addr F + o, writable *)
Definition w14_rsh (o : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 20%nat) o (o + 1) o (o + 1) cs.
Definition w14_rs : smem :=
  [w14_rframe; w14_rhz; w14_robj 0x190 []; w14_robj 0x1a0 []; w14_rsh 0x32 []; w14_rsh 0x34 []].
Definition w14_extra (e : rt_renv) (hz : Z) : list word :=
  [w64 (q_b3 e); w64 (Z.shiftl (q_b6 e) 8); w64 (q_b5 e); w64 (Z.shiftl (q_b4 e) 8); w64 (q_mask e);
   w64 (hz mod 2 ^ 32)].
(* the value the run stores to asked[1]: (b4 << 8 | b3) | (b6 << 8 | b5) << 16 over the cells' atoms *)
Definition w14_other_sv : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SOff 35 0) (SOff 32 0)) (SAlu ALU_SLL (SAlu ALU_OR (SOff 33 0) (SOff 34 0)) (SLit 16)).
(* the run's four write windows: asked[0], asked[1] and their two shadow bytes *)
Definition w14_wr (F : Z) (a : Z) : Prop :=
  (F + 0x190 <= a < F + 0x194) \/ (F + 0x1a0 <= a < F + 0x1a4) \/
  a = shadow_addr F + 0x32 \/ a = shadow_addr F + 0x34.

(* ======================================= arithmetic ======================================= *)
(* 0x82ce0 slli a2,s10,62; 0x82cf8 srli s5,a2,63: s5 = bit 1 of the flags byte, over its 256 values *)
Lemma w14_bits_all : forallb (fun n =>
  bv_eqb (alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 62)) (Z_to_bv 64 63))
    (Z_to_bv 64 (Z.b2z (Z.testbit (Z.of_nat n) 1)))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w14_bit1 : forall fl, 0 <= fl < 256 ->
alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 fl) (Z_to_bv 64 62)) (Z_to_bv 64 63) = Z_to_bv 64 (Z.b2z (Z.testbit fl 1)).
Proof.
intros fl Hfl. pose proof w14_bits_all as H. rewrite forallb_forall in H.
specialize (H (Z.to_nat fl) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply bv_eqb_eq in H. exact H.
Qed.

(* `or` of a byte and a byte shifted by 8 *)
Lemma w14_lor8 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (Z.shiftl y 8) x = x + 256 * y.
Proof.
intros x y Hx Hy. rewrite Z.lor_comm. rewrite lor_shiftl_add by (cbn; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. ring.
Qed.
Lemma w14_other_val : forall e, rt_hdr_ok e ->
rs_other e = q_b3 e + 256 * q_b4 e + 65536 * (q_b5 e + 256 * q_b6 e).
Proof.
intros e (_ & _ & _ & H3 & H4 & H5 & H6). unfold rs_other.
rewrite (w14_lor8 (q_b3 e) (q_b4 e)) by lia. rewrite (w14_lor8 (q_b5 e) (q_b6 e)) by lia.
rewrite lor_shiftl_add by (cbn; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536. ring.
Qed.
Lemma w14_U_other : forall E b3 b4 b5 b6,
ew E 32 = Z_to_bv 64 b3 -> ew E 33 = Z_to_bv 64 (Z.shiftl b6 8) -> ew E 34 = Z_to_bv 64 b5 ->
ew E 35 = Z_to_bv 64 (Z.shiftl b4 8) ->
0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
U E w14_other_sv = b3 + 256 * b4 + 65536 * (b5 + 256 * b6).
Proof.
intros E b3 b4 b5 b6 E32 E33 E34 E35 H3 H4 H5 H6.
assert (S4 : Z.shiftl b4 8 = 256 * b4) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; ring).
assert (S6 : Z.shiftl b6 8 = 256 * b6) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; ring).
unfold w14_other_sv. rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom E 35 _ E35) by (rewrite S4; lia). rewrite (U_atom E 32 _ E32) by lia.
rewrite (U_atom E 33 _ E33) by (rewrite S6; lia). rewrite (U_atom E 34 _ E34) by lia.
rewrite (w14_lor8 b3 b4) by lia. rewrite (w14_lor8 b5 b6) by lia.
change (Z.land (zcanon 16) 63) with 16.
rewrite (zcanon_id (b3 + 256 * b4)) by (unfold M64; lia).
rewrite (zcanon_id (b5 + 256 * b6)) by (unfold M64; lia).
assert (SH : Z.shiftl (b5 + 256 * b6) 16 = (b5 + 256 * b6) * 65536)
by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
rewrite (zcanon_id (Z.shiftl (b5 + 256 * b6) 16)) by (rewrite SH; unfold M64; lia).
rewrite lor_shiftl_add by (cbn; lia). rewrite SH. rewrite zcanon_id by (unfold M64; lia). ring.
Qed.

(* the low 4 bytes of a sign-extended 32-bit value are the value *)
Lemma w14_sext32_low : forall c, 0 <= c < 2 ^ 32 -> zcanon (bv_swrap 32 c) mod 2 ^ 32 = c.
Proof.
intros c Hc. unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
change (2 ^ 32) with 4294967296 in *. change (2 ^ 64) with 18446744073709551616.
destruct (Z.lt_ge_cases c 2147483648) as [Hl|Hg].
- rewrite (Z.mod_small (c + 2147483648) 4294967296) by lia.
  replace (c + 2147483648 - 2147483648) with c by ring.
  rewrite (Z.mod_small c 18446744073709551616) by lia. apply Z.mod_small. lia.
- rewrite <- (Z.mod_unique (c + 2147483648) 4294967296 1 (c - 2147483648)) by lia.
  rewrite <- (Z.mod_unique (c - 2147483648 - 2147483648) 18446744073709551616 (-1)
    (c - 4294967296 + 18446744073709551616)) by lia.
  rewrite <- (Z.mod_unique (c - 4294967296 + 18446744073709551616) 4294967296 4294967295 c) by lia.
  reflexivity.
Qed.

(* the parse's answer is rc = 1, 0 or -1 (Rate.answer_ok of the parse and of the NULL answer) *)
Lemma w14_rc3 : forall null bs,
snd (Rate.harness_parse null bs) = 1 \/ snd (Rate.harness_parse null bs) = 0 \/
snd (Rate.harness_parse null bs) = -1.
Proof.
intros null bs. unfold Rate.harness_parse. destruct null; [right; right; reflexivity|].
pose proof (Rate.parse_model_shape bs) as H.
destruct (Rate.parse_model bs) as [[v|] r]; cbn [snd Rate.answer_ok] in H |- *.
- left. exact (proj1 H).
- destruct H as [-> | ->]; [right; left | right; right]; reflexivity.
Qed.

(* the frame's shadow: rs_PZ with granules 50 and 52 set to 4 is rs_PB *)
Lemma w14_PZ_PB : forall i : nat, (i < 56)%nat -> i <> 50%nat -> i <> 52%nat -> nth i rs_PB 0 = nth i rs_PZ 0.
Proof.
intros i Hi H50 H52.
assert (H : forallb (fun j => (Nat.eqb j 50 || Nat.eqb j 52 || Z.eqb (nth j rs_PB 0) (nth j rs_PZ 0))%bool)
  (seq 0 56) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H i ltac:(apply in_seq; lia)).
apply Bool.orb_prop in H as [H|H]; [apply Bool.orb_prop in H as [H|H]|].
- apply Nat.eqb_eq in H. lia.
- apply Nat.eqb_eq in H. lia.
- apply Z.eqb_eq in H. exact H.
Qed.
Lemma w14_fsh_PB : forall H mem H' mem' F,
rt_fsh rsegs H mem F rs_PZ ->
aview rsegs H' mem' (shadow_addr F + 50) = Some 4 -> aview rsegs H' mem' (shadow_addr F + 52) = Some 4 ->
(forall i, 0 <= i < 56 -> i <> 50 -> i <> 52 -> aview rsegs H' mem' (shadow_addr F + i) = aview rsegs H mem (shadow_addr F + i)) ->
rt_fsh rsegs H' mem' F rs_PB.
Proof.
intros H mem H' mem' F Hz S50 S52 K i Hi. change (Z.of_nat (length rs_PB)) with 56 in Hi.
destruct (Z.eq_dec i 50) as [->|N50]; [rewrite S50; reflexivity|].
destruct (Z.eq_dec i 52) as [->|N52]; [rewrite S52; reflexivity|].
rewrite (K i Hi N50 N52). rewrite (Hz i ltac:(change (Z.of_nat (length rs_PZ)) with 56; lia)).
f_equal. symmetry. apply w14_PZ_PB; lia.
Qed.

(* ======================================= the run ======================================= *)
(* the write-range obligation: the two read-only regions, the two frame objects (atom 22 = F) and the two shadow
   bytes (atom 20 = shadow_addr F) of the frame (3, pos) the harness holds *)
Ltac w14_awr_obj :=
lazymatch goal with E22 : bv_unsigned (ew _ 22) = _, FLY : frame_addr _ 3 ?pos = _, Hown : In (3, ?pos) (x_own _ _) |- _ =>
eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 22%nat pos 0);
[reflexivity | rewrite E22, FLY; ring | exact Hown | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | ]
end.
Ltac w14_awr_sh :=
lazymatch goal with E20 : bv_unsigned (ew _ 20) = _, FLY : frame_addr _ 3 ?pos = _, Hown : In (3, ?pos) (x_own _ _) |- _ =>
eapply (rts_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 20%nat pos);
[reflexivity | rewrite E20, FLY; reflexivity | exact Hown | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | ]
end.
Ltac w14_awr :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
w14_awr_obj; w14_awr_obj; w14_awr_sh; w14_awr_sh; apply awr_ok_nil.
(* every write window of the run lies in w14_wr *)
Ltac w14_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
unfold w14_wr;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  lazymatch goal with E9 : bv_unsigned (ew _ 9) = _, E20 : bv_unsigned (ew _ 20) = _,
    E21 : bv_unsigned (ew _ 21) = _, E22 : bv_unsigned (ew _ 22) = _ |- _ =>
    rewrite ?E9, ?E20, ?E21, ?E22 in Hb end; lia | ]);
destruct Hr.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* asked[]'s writes are in M02's write set *)
Lemma w14_wr_E2 : forall (cx : rs_scx rsegs) a, w14_wr (q_F (x_e rsegs cx)) a -> rs_E2 rsegs cx a.
Proof.
intros cx a Hw. unfold rs_E2, rt_inw. left. cbn [hi_w2 rate_himg_A]. rewrite !Exists_cons.
unfold w14_wr in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- right; left. cbn [rt_xv fst snd]. lia.
- right; right; left. cbn [rt_xv fst snd]. lia.
- right; right; right; right; left. cbn [rt_xv fst snd]. lia.
- right; right; right; right; right; left. cbn [rt_xv fst snd]. lia.
Qed.

(* what reaching DEC from the set-up means: rs_core, s0 / s1 / s2 / s4 as at A, the seven registers turn 0 reads,
   every byte outside the four write windows as at A, the two shadow bytes in scope, and asked[] filled *)
Definition w14_AK (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec)
(regs0 : bvmap 5 word) (W0 : world rsegs) (mem0 : word -> option byte) : Prop :=
forall ly3 S3 regs3 mem3 md3,
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W0 regs3 mem3 md3 ->
cs_eq [8; 9; 18; 20]%bv regs0 regs3 ->
getr regs3 (Z_to_bv 5 10) = w64 (q_F (x_e rsegs cx) + 0x190) -> getr regs3 (Z_to_bv 5 19) = w64 1 ->
getr regs3 (Z_to_bv 5 21) = w64 (Z.b2z (Z.testbit (q_fl (x_e rsegs cx)) 1)) ->
getr regs3 (Z_to_bv 5 22) = w64 (q_F (x_e rsegs cx) + 0x1a0) ->
getr regs3 (Z_to_bv 5 26) = w64 (q_mask (x_e rsegs cx)) -> getr regs3 (Z_to_bv 5 27) = w64 RS_CLOSED ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w14_wr (q_F (x_e rsegs cx)) a ->
 aview rsegs (w_H W0) mem3 a = aview rsegs (w_H W0) mem0 a) ->
aview rsegs (w_H W0) mem3 (shadow_addr (q_F (x_e rsegs cx)) + 50) = Some 4 ->
aview rsegs (w_H W0) mem3 (shadow_addr (q_F (x_e rsegs cx)) + 52) = Some 4 ->
rs_ask_at rsegs cx rec W0 mem3 ->
SRr rsegs W0 (cfg_at rsegs RS_DEC regs3 mem3 md3) POST.

Lemma w14_set : forall (cx : rs_scx rsegs) POST rec ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 22, q_F (x_e rsegs cx));
                          (LReg 26, q_fl (x_e rsegs cx)); (LCell XR 0x78, q_F (x_e rsegs cx));
                          (LCell XR 0xc0, q_pp (x_e rsegs cx))]) ->
rs_hz_at rsegs cx rec W2 mem2 ->
w14_AK cx POST rec regs2 W2 mem2 ->
SRr rsegs W2 (cfg_at rsegs RS_A regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST rec ly2 S2 W2 regs2 mem2 md2 Hpre Hcore Hat Hhz HK.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w14_wx as Hwx. pose proof w14_segs_low as Hsegs.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof (rts_fbounds _ F32 Fapp) as (_ & _ & S0 & S64 & Ssep & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in Hwin, Hceil.
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & _ & Hhdr & _).
cbn [hi_cid rate_himg_A] in Hown, HF.
pose proof Hhdr as (Hfl & Hmask & _ & Hb3 & Hb4 & Hb5 & Hb6).
pose proof (proj1 Hcore) as HJ.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfr2 & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HJ0 as (_ & Hlyc & _).
assert (FLY : frame_addr ly2 3 (x_pos rsegs cx) = q_F (x_e rsegs cx)).
{ rewrite HF. unfold frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & L2 & _).
  destruct Hlyc as (_ & _ & _ & _ & _ & Lc & _). rewrite L2, Lc. reflexivity. }
clear HJ0.
assert (Hin3 : In (3, x_pos rsegs cx) (frames S2)) by (rewrite Hfr2; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin3) as (_ & _ & Hfob & Hfsh).
rewrite FLY in Hfob, Hfsh. change (fs_frame_bytes 3) with 512 in Hfob. change (fs_frame_bytes 3 / 8) with 64 in Hfsh.
clear HAR2.
(* the cut's registers and cells *)
unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc in Hat. cbv zeta in Hat. rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as (((A8 & A9 & A20 & A18 & C138 & A21 & C18 & C58 & _) & (C20 & C38 & C40 & C48 & C50 & C120 & _)) &
  A24 & A22 & A26 & C78 & Cc0 & _).
cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, A21, A24, A22, A26, C20, C38, C40, C48, C120.
assert (Sh4 : 0 <= Z.shiftl (q_b4 (x_e rsegs cx)) 8 < 65536)
by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
assert (Sh6 : 0 <= Z.shiftl (q_b6 (x_e rsegs cx)) 8 < 65536)
by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
rewrite Z.mod_small in C20, C38, C40, C48, C120 by lia.
pose proof (Z.mod_pos_bound (rs_hz rsegs cx rec) (2 ^ 32) ltac:(lia)) as Hhz32.
(* the entry state's env facts *)
set (X := w14_extra (x_e rsegs cx) (rs_hz rsegs cx rec)).
assert (E9 : bv_unsigned (ew (Ereg regs2 X) 9) = q_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). assert (G : getr regs2 9%bv = w64 (q_R (x_e rsegs cx))) by exact A9.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E20 : bv_unsigned (ew (Ereg regs2 X) 20) = shadow_addr (q_F (x_e rsegs cx))).
{ rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl).
  assert (G : getr regs2 20%bv = w64 (shadow_addr (q_F (x_e rsegs cx)))) by exact A20.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E21 : bv_unsigned (ew (Ereg regs2 X) 21) = q_F (x_e rsegs cx) + 0x180).
{ rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl).
  assert (G : getr regs2 21%bv = w64 (q_F (x_e rsegs cx) + 0x180)) by exact A21.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E22 : bv_unsigned (ew (Ereg regs2 X) 22) = q_F (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl). assert (G : getr regs2 22%bv = w64 (q_F (x_e rsegs cx))) by exact A22.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E26 : ew (Ereg regs2 X) 26 = w64 (q_fl (x_e rsegs cx))).
{ rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl). exact A26. }
assert (X32 : ew (Ereg regs2 X) 32 = w64 (q_b3 (x_e rsegs cx))) by exact (ew_Ereg_extra regs2 X 0).
assert (X33 : ew (Ereg regs2 X) 33 = w64 (Z.shiftl (q_b6 (x_e rsegs cx)) 8)) by exact (ew_Ereg_extra regs2 X 1).
assert (X34 : ew (Ereg regs2 X) 34 = w64 (q_b5 (x_e rsegs cx))) by exact (ew_Ereg_extra regs2 X 2).
assert (X35 : ew (Ereg regs2 X) 35 = w64 (Z.shiftl (q_b4 (x_e rsegs cx)) 8)) by exact (ew_Ereg_extra regs2 X 3).
assert (X36 : ew (Ereg regs2 X) 36 = w64 (q_mask (x_e rsegs cx))) by exact (ew_Ereg_extra regs2 X 4).
assert (X37 : ew (Ereg regs2 X) 37 = w64 (rs_hz rsegs cx rec mod 2 ^ 32)) by exact (ew_Ereg_extra regs2 X 5).
(* the regions *)
assert (HRS : Forall (region_ok rsegs (Ereg regs2 X) (mrestrict (w_H W2) mem2)) w14_rs).
{ unfold w14_rs. repeat apply Forall_cons; try apply Forall_nil.
  - unfold w14_rframe.
    apply (m2_frame_ok _ W2 mem2 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val rsegs _ _ _ 0x20 8 (SOff 32 0) (q_b3 (x_e rsegs cx)));
      [apply rts_den_atom; [exact X32 | lia] | cbn; lia | cbn; lia | exact C20].
    + apply (chunk_ok_val rsegs _ _ _ 0x38 8 (SOff 33 0) (Z.shiftl (q_b6 (x_e rsegs cx)) 8));
      [apply rts_den_atom; [exact X33 | lia] | cbn; lia | cbn; lia | exact C38].
    + apply (chunk_ok_val rsegs _ _ _ 0x40 8 (SOff 34 0) (q_b5 (x_e rsegs cx)));
      [apply rts_den_atom; [exact X34 | lia] | cbn; lia | cbn; lia | exact C40].
    + apply (chunk_ok_val rsegs _ _ _ 0x48 8 (SOff 35 0) (Z.shiftl (q_b4 (x_e rsegs cx)) 8));
      [apply rts_den_atom; [exact X35 | lia] | cbn; lia | cbn; lia | exact C48].
    + apply (chunk_ok_val rsegs _ _ _ 0x120 8 (SOff 36 0) (q_mask (x_e rsegs cx)));
      [apply rts_den_atom; [exact X36 | lia] | cbn; lia | cbn; lia | exact C120].
  - unfold w14_rhz.
    apply (m2_hzcell_ok _ W2 mem2 (q_F (x_e rsegs cx)) (SOff 37 0) (rs_hz rsegs cx rec mod 2 ^ 32));
    [exact E21 | lia | lia | apply rts_den_atom; [exact X37 | lia] | lia | exact Hhz].
  - unfold w14_robj. apply (rtm_rw_region rsegs _ (w_H W2) mem2 22 (q_F (x_e rsegs cx)));
    [exact E22 | lia | lia | | apply Forall_nil].
    intros o Ho. destruct (Hfob (q_F (x_e rsegs cx) + o) ltac:(lia)) as [Hpo _]. exact Hpo.
  - unfold w14_robj. apply (rtm_rw_region rsegs _ (w_H W2) mem2 22 (q_F (x_e rsegs cx)));
    [exact E22 | lia | lia | | apply Forall_nil].
    intros o Ho. destruct (Hfob (q_F (x_e rsegs cx) + o) ltac:(lia)) as [Hpo _]. exact Hpo.
  - unfold w14_rsh. apply (rtm_rw_region rsegs _ (w_H W2) mem2 20 (shadow_addr (q_F (x_e rsegs cx))));
    [exact E20 | lia | lia | | apply Forall_nil].
    intros o Ho. destruct (Hfsh o ltac:(lia)) as [Hpo _]. exact Hpo.
  - unfold w14_rsh. apply (rtm_rw_region rsegs _ (w_H W2) mem2 20 (shadow_addr (q_F (x_e rsegs cx))));
    [exact E20 | lia | lia | | apply Forall_nil].
    intros o Ho. destruct (Hfsh o ltac:(lia)) as [Hpo _]. exact Hpo. }
assert (HPD : pairwise_disjoint (Ereg regs2 X) w14_rs).
{ unfold w14_rs, w14_rframe, w14_rhz, w14_robj, w14_rsh, m2_frame, m2_hzcell.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E20, E21, E22.
  repeat split; lia. }
pose proof (m2_facts_ok (Ereg regs2 X) (q_R (x_e rsegs cx)) E9 ltac:(lia) Hal) as HG.
(* the three answers of the parse *)
destruct (w14_rc3 (Z.testbit (q_fl (x_e rsegs cx)) 0) (buf rec)) as [Hrc|[Hrc|Hrc]];
change (Rate.harness_parse (Z.testbit (q_fl (x_e rsegs cx)) 0) (buf rec)) with (rs_PA rsegs cx rec) in Hrc;
rewrite Hrc in A24;
lazymatch type of A24 with _ = w64 ?v =>
pose proof (m2_entry RS_A [((24%bv : bv 5), SLit v)] w14_rs m2_facts W2 regs2 X mem2) as HS;
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
  [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
  | rewrite ck_lit; symmetry; exact A24]) ltac:(vm_compute; reflexivity) HRS HPD HG)
end;
remember (Ereg regs2 X) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs2 X) E) by (subst E; apply env_agree_refl);
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w14_wr (q_F (x_e rsegs cx)) a ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity);
unfold cfg_at; change (w64 RS_A) with (Z_to_bv 64 RS_A);
w14_run idtac.
1,3,5: w14_awr.
all: ck_keep w14_kwr.
all: let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
all: let R := fresh "R19" in rreg HS (19%bv : bv 5) R.
all: let R := fresh "R21" in rreg HS (21%bv : bv 5) R.
all: let R := fresh "R22" in rreg HS (22%bv : bv 5) R.
all: let R := fresh "R26" in rreg HS (26%bv : bv 5) R.
all: let R := fresh "R27" in rreg HS (27%bv : bv 5) R.
all: lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [8; 9; 18; 20]%bv HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  pose proof (rts_region_nth E ss ms 2 _ H HS eq_refl) as G0;
  pose proof (rts_region_nth E ss ms 3 _ H HS eq_refl) as G1;
  pose proof (rts_region_nth E ss ms 4 _ H HS eq_refl) as G2;
  pose proof (rts_region_nth E ss ms 5 _ H HS eq_refl) as G3;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with RS_DEC by (vm_compute; reflexivity)
  end.
all: lazymatch goal with HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (HK ly2 S2 (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ'
      (w14_r234 _ _ C234) eq_refl (Permutation_refl _)); [m2_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ He; apply KE; [exact Ha | intros Hw; exact (He (w14_wr_E2 cx a Hw))]
  | exact CL | | | | | | | exact KE | | | ]
  end.
(* a0 = F + 0x190, s3 = 1, s5 = the role, s6 = F + 0x1a0, s10 = mask, s11 = closed_list *)
all: try (etransitivity; [exact R10|]; rewrite E22; reflexivity).
all: try exact R19.
all: try (etransitivity; [exact R21|]; rewrite E26; exact (w14_bit1 _ Hfl)).
all: try (etransitivity; [exact R22|]; rewrite E22; reflexivity).
all: try (etransitivity; [exact R26|]; exact X36).
all: try exact R27.
(* the two shadow bytes *)
all: try (cbn [YP09.r_base] in G2; apply (rtm_val1_aview rsegs);
  [ refine (val_of_chunk_ok rsegs E _ _ 0x32 1 (SLit 4) 4 _ eq_refl ltac:(cbn; lia) ltac:(cbn; lia));
    exact (rts_chunks E _ 20 _ _ _ _ _ _ G2 E20 _ (or_introl eq_refl))
  | lia ]).
all: try (cbn [YP09.r_base] in G3; apply (rtm_val1_aview rsegs);
  [ refine (val_of_chunk_ok rsegs E _ _ 0x34 1 (SLit 4) 4 _ eq_refl ltac:(cbn; lia) ltac:(cbn; lia));
    exact (rts_chunks E _ 20 _ _ _ _ _ _ G3 E20 _ (or_introl eq_refl))
  | lia ]).
(* asked[0] and asked[1] *)
all: split.
all: try (refine (val_of_chunk_ok rsegs E _ _ 0x1a0 4 w14_other_sv (rs_other (x_e rsegs cx)) _ _ _ ltac:(cbn; lia));
  [ exact (rts_chunks E _ 22 _ _ _ _ _ _ G1 E22 _ (or_introl eq_refl))
  | rewrite denot_lit_U; f_equal;
    rewrite (w14_U_other E _ _ _ _ X32 X33 X34 X35 Hb3 Hb4 Hb5 Hb6), (w14_other_val _ Hhdr); reflexivity
  | rewrite (w14_other_val _ Hhdr); cbn; lia ]).
(* asked[0]: rc = 1 stores the hz atom sign-extended, else 48000 *)
all: assert (A0 : rs_ask0 rsegs cx rec = if snd (rs_PA rsegs cx rec) =? 1 then rs_hz rsegs cx rec else 48000)
  by reflexivity.
all: rewrite A0, Hrc; cbn [Z.eqb Pos.eqb].
- intros k Hk.
  refine (YN0d.chunk_bytes_cval rsegs E _ _ 0x190 4 (SExt true 32 (SOff 37 0)) _ _ _ k Hk).
  + exact (rts_chunks E _ 22 _ _ _ _ _ _ G0 E22 _ (or_introl eq_refl)).
  + change (bv_unsigned (sv_denot E (SExt true 32 (SOff 37 0)))) with (U E (SExt true 32 (SOff 37 0))).
    rewrite U_SExt. cbv iota beta. rewrite (U_atom E 37 _ X37 ltac:(lia)).
    change (8 * Z.of_N 4) with 32. change (Z.of_N 32) with 32.
    rewrite (Z.mod_small (rs_hz rsegs cx rec mod 2 ^ 32) (2 ^ 32)) by lia.
    rewrite w14_sext32_low by lia. rewrite ?Z.mod_mod by lia. reflexivity.
- change (48000 mod 2 ^ 32) with 48000.
  refine (val_of_chunk_ok rsegs E _ _ 0x190 4 (SLit 48000) 48000 _ eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  exact (rts_chunks E _ 22 _ _ _ _ _ _ G0 E22 _ (or_introl eq_refl)).
- change (48000 mod 2 ^ 32) with 48000.
  refine (val_of_chunk_ok rsegs E _ _ 0x190 4 (SLit 48000) 48000 _ eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  exact (rts_chunks E _ 22 _ _ _ _ _ _ G0 E22 _ (or_introl eq_refl)).
Qed.
End w.

(* ======================================= the piece statement ======================================= *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the DEC cut at turn 0 from the A cut's facts and what the set-up gives *)
Lemma w14_cut_DEC : forall (cx : rs_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_cut_A (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W2 regs3 mem3 md3 ->
cs_eq [8; 9; 18; 20]%bv regs2 regs3 ->
getr regs3 (Z_to_bv 5 10) = w64 (q_F (x_e rsegs cx) + 0x190) -> getr regs3 (Z_to_bv 5 19) = w64 1 ->
getr regs3 (Z_to_bv 5 21) = w64 (Z.b2z (Z.testbit (q_fl (x_e rsegs cx)) 1)) ->
getr regs3 (Z_to_bv 5 22) = w64 (q_F (x_e rsegs cx) + 0x1a0) ->
getr regs3 (Z_to_bv 5 26) = w64 (q_mask (x_e rsegs cx)) -> getr regs3 (Z_to_bv 5 27) = w64 RS_CLOSED ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w14_wr (q_F (x_e rsegs cx)) a ->
 aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
aview rsegs (w_H W2) mem3 (shadow_addr (q_F (x_e rsegs cx)) + 50) = Some 4 ->
aview rsegs (w_H W2) mem3 (shadow_addr (q_F (x_e rsegs cx)) + 52) = Some 4 ->
rs_ask_at rsegs cx rec W2 mem3 ->
rs_cut_DEC (fx := fx) rsegs B MT cx fx2 rec 0 ly3 S3 W2 regs3 mem3 md3.
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 regs3 mem3 md3 Hpre (Hbase & Hat & _) Hcore3 HL
H10 H19 H21 H22 H26 H27 K3 S50 S52 Hask.
destruct Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w14_segs_low as Hsegs.
pose proof (m2_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof (rts_fbounds _ F32 Fapp) as (_ & _ & S0 & S64 & Ssep & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in Hceil.
assert (FD : 0 <= q_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
assert (HF8 : q_F (x_e rsegs cx) = 8 * (q_F (x_e rsegs cx) / 8)).
{ pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D.
  assert (q_F (x_e rsegs cx) mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide _ 32 8) by (exists 4; lia); rewrite F32; reflexivity).
  lia. }
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & Hppin & _).
cbn [hi_cid rate_himg_A] in Hown, HF.
pose proof HJ0 as (HAR0 & _ & _ & _ & _ & Hfr0 & _).
assert (Hin3 : In (3, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfr0; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hppin Hin3) as Zpf.
unfold zdisjoint in Zpf. cbn [fst snd] in Zpf. rewrite <- HF in Zpf. change (fs_frame_bytes 3) with 512 in Zpf.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Zpf.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hppin) as (_ & P4096 & Pceil & Papp & _).
rewrite Hrq in Papp, Pceil.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
(* the bytes the cut names lie outside the write windows *)
assert (Wfar : forall a, alloc_ceiling <= a -> ~ w14_wr (q_F (x_e rsegs cx)) a).
{ intros a Ha Hw. unfold w14_wr in Hw. lia. }
unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc in Hat. cbv zeta in Hat. rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as (((A8 & A9 & A20 & A18 & C138 & A21 & C18 & C58 & _) & (C20 & C38 & C40 & C48 & C50 & C120 & _)) &
  A24 & A22 & A26 & C78 & Cc0 & _).
cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, C138, C18, C50, C120, C78, Cc0.
assert (Kc : forall o v, 0 <= o < 0x1e0 ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + o) 8 v).
{ intros o v Ho Hv. eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | apply Wfar; lia]. }
split; [|split; [|split; [exact Hask | lia]]].
- (* rs_chk_base at rs_PB *)
  split; [exact Hcore3|]. split; [exact Hfxk|].
  split.
  { unfold rs_fsh_at in *. apply (w14_fsh_PB _ _ _ _ _ Hfsh S50 S52). intros i Hi N50 N52.
    apply K3; [lia|]. unfold w14_wr. lia. }
  split.
  { apply (rtm_rom_kept rsegs W2 W2 mem2 mem3 Hrom). intros a Ha.
    assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    apply K3; [lia|]. unfold w14_wr, shadow_addr, SHADOW_OFF. intros [Hw|[Hw|[Hw|Hw]]];
    [exact (Fimg a ltac:(lia) Hi) | exact (Fimg a ltac:(lia) Hi) | lia | lia]. }
  split.
  { unfold rs_pp_at in *. intros j Hj. destruct (Hpp j Hj) as (Hv & Hr). split; [|exact Hr].
    unfold rs_u8s in Hj. rewrite length_map in Hj. pose proof (Layout.length_pp_bytes rec Hwf) as HL0.
    eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 1) with 1 in Hk.
    apply K3; [lia|]. unfold w14_wr, shadow_addr, SHADOW_OFF. lia. }
  split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hpod0|]. split; [exact Hpod | exact Hpod1].
- (* the turn-0 values *)
  unfold rs_at_cx, rs_at, rs_L_DEC, rs_L_dec. cbv zeta. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
  + etransitivity; [exact (HL 8%bv ltac:(cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
    exact A8.
  + etransitivity; [exact (HL 9%bv ltac:(cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
    exact A9.
  + etransitivity; [exact (HL 20%bv ltac:(cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
    exact A20.
  + exact (Kc 0x18 _ ltac:(lia) C18).
  + exact (Kc 0x50 _ ltac:(lia) C50).
  + exact (Kc 0x78 _ ltac:(lia) C78).
  + exact (Kc 0xc0 _ ltac:(lia) Cc0).
  + exact (Kc 0x120 _ ltac:(lia) C120).
  + exact (Kc 0x138 _ ltac:(lia) C138).
  + etransitivity; [exact (HL 18%bv ltac:(cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
    exact A18.
  + rewrite H10; f_equal; lia.
  + rewrite H19; f_equal; lia.
  + exact H21.
  + exact H22.
  + exact H26.
  + exact H27.
Qed.

(* ---- W14 ASKED: A 0x82ca8 -> DEC 0x82d14, turn 0 ---- *)
Theorem rt_w14_asked_A : rs_piece_W14_asked_stmt rsegs B MT.
Proof using MTL.
unfold rs_piece_W14_asked_stmt. intros cx POST inp Hst HDEC.
unfold rs_from_A. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HA.
destruct Hst as (Hpre & _).
pose proof HA as (Hbase & Hat & Hhz). pose proof Hbase as (Hcore & _).
apply (w14_set (fx := fx2) B MT MTL cx POST rec ly2 S2 W2 regs2 mem2 md2 Hpre Hcore Hat Hhz).
intros ly3 S3 regs3 mem3 md3 Hcore3 HL H10 H19 H21 H22 H26 H27 K3 S50 S52 Hask.
apply (HDEC fx2 ly3 S3 W2 regs3 mem3 md3 rec).
exact (w14_cut_DEC cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 regs3 mem3 md3 Hpre HA Hcore3 HL
  H10 H19 H21 H22 H26 H27 K3 S50 S52 Hask).
Qed.
End m.

Print Assumptions rt_w14_asked_A.
About rt_w14_asked_A.
