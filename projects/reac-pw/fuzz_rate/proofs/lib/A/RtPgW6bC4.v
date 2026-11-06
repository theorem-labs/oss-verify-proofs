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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 174 of its 211 lines of code are new or changed and 253 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aTail.v at e261793226b4; ported to reac-pw/fuzz_rate's image A: module paths changed (images.Asan for lib/A/Img0, RtPgBase / RtPgCSpec / RtPgSteps / RtPgW6aBase for the RPg files, RtPgSteps' rts_wx / rts_segs_low / same_io_wvb / regs_kept_of_st_ok / rts_post for RPgCfgChanges' and RPgSteps' facts and w6_post); rate's pcs and the cell [R+0x138] for [R+0xf0]; rate's tail stores in.n to s8 (`mv s8,a1`) instead of the cell [R+0xf8], so the s1-based region is read-only, the post has three stored values and s8 in place of s9; the frame facts use the kit's AR_laws_ok instead of a LAWS hypothesis. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aTail.v, with its module paths and module names changed; 405 of its 470 lines of code are new or changed and 146 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the block lemma w6b_c4 of
   lib/A/RtPgW6bBase.v, case 4 of ent_build's `switch (kind % 10)` (pod.h:326-330) inside LLVMFuzzerTestOneInput,
   from its entry 0x81668 to the join J 0x81e00. Proves no function (kind: segment lemma).

   THE CODE (registers as in RtPgW6bBase.v: s1 = R, s2 = SHADOW_OFF, s9 = c the cursor, s8 = |r|, a4 = c - 1,
   a5 = |r| + 1):
     0x81668  beqz s8 -> 0x81994                     no byte left: v = 0
     0x8166c .. 0x81674  the shadow check of s9 (NE-SLOW, slow block 0x82170 `andi a1,s9,7; blt a1,a0`)
     0x81678  ld s6,0xe8(s1)                         between the check's load and its branch
     0x81680  lbu a0,0(s9) (= v); s8 := a5 - 2; s9 := a4 + 2
     0x8168c .. 0x816a4  a0 := (v - (v * 0xab >> 9) - 2 * (v * 0xab >> 9)) & 0xff   (= v mod 3, pod.h:327)
     0x816a8  j 0x8199c
     0x81994  a0 := 0; ld s6,0xe8(s1)                (then 0x8199c)
     0x8199c  ld a1,0x138(s1) (= &e); sw 2,0(a1) (e.type = POD_BOOL); sw 4,4(a1) (e.size = 4);
              sw a0,8(a1) (e.body[0..4) = v mod 3); 0x819b4 j 0x81e00 (J)
   THE PROOF is one engine run per arm (lib/Reusable/YCbn.v, the token engine that follows the NE-SLOW slow block
   itself and leaves one obligation `range_addressable ...` per check, paid by obl_of_range):
     the entry state (c4_entry) has the extra atoms 32 = &e = F + 0xf0, 33 = the value of [R+0xe8], 34 = the input
     byte; the regions are e (based at atom 32, write window [0, 12)), the two real-frame cells [R+0xe8] and
     [R+0x138] (based at s1, read only, each inside one of the two spans w6_in keeps the input out of), and the
     input byte at s9 (based at atom 25, read only, only when a byte is left). The shadow entry [mkSHE 32 0 0x68]
     makes e's write window safe against the shadow band (c4_shok, from w6b_in's range_addressable and in_app).
     With no byte left s8 is pinned to the literal 0, so `beqz` is taken and no check runs.
     The `mod 3` arithmetic is checked for all 256 byte values by computation (c4_all256, c4_a0_val). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSteps RtPgW6aBase RtPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgMem.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments, as RtPgSteps names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the entry state ========================================
   extra atoms: 32 = F + 0xf0 (&e), 33 = the value of [R+0xe8], 34 = the input byte *)
Definition c4_extra (F vb m : Z) : list word := [Z_to_bv 64 (F + 0xf0); Z_to_bv 64 vb; Z_to_bv 64 m].
Definition C4Bx : sv := SOff 18 0.
Definition C4span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition c4_SH : list shent := [mkSHE 32 0 0x68].
(* e = [F+0xf0, F+0x158): the block writes its first 12 bytes *)
Definition c4_rE : YP09.region := YP09.mkRegion (Some 32%nat) 0 0x68 0 12 [].
(* [R+0xe8] = vb, inside [R+0x60, R+0x120) *)
Definition c4_rA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xe8 0xf0 0 0 [YP09.mkChunk 0xe8 (CVal 8 (SOff 33 0))].
(* [R+0x138] = F + 0xf0, inside [R+0x128, R+0x140) *)
Definition c4_rB : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x138 0x140 0 0 [YP09.mkChunk 0x138 (CVal 8 (SOff 32 0))].
(* the input byte at the cursor *)
Definition c4_rI : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition c4_regs (byte : bool) : smem := if byte then [c4_rE; c4_rA; c4_rB; c4_rI] else [c4_rE; c4_rA; c4_rB].
Definition c4_facts1 : facts :=
  mkFacts [ (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 2 (2 ^ 47 - 1) 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 1024) 0); (24%nat, mkAF 1 (2 ^ 47) 0); (34%nat, mkAF 0 255 0) ] [] [].
Definition c4_facts0 : facts :=
  mkFacts [ (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 2 (2 ^ 47 - 1) 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 1024) 0) ] [] [].
Definition c4_facts (byte : bool) : facts := if byte then c4_facts1 else c4_facts0.
Definition c4_ss (byte : bool) : sstate := mkSS W6B_D4 sr_atoms (c4_regs byte) None (c4_facts byte).

(* ======================================== the arithmetic ========================================
   a0 at 0x816a8, as the engine computes it from the input byte (atom 34): the `mul 0xab` / `srli 9` quotient
   q = v / 3, then v - q - 2 q, masked to a byte. *)
Definition c4_q : sv := SAlu ALU_SRL (SMd M_MUL (SOff 34 0) (SLit 171)) (SLit 9).
Definition c4_a0 : sv :=
  SAlu ALU_AND (SAlu ALU_SUB (SAlu ALU_SUB (SOff 34 0) c4_q) (SAlu ALU_SLL c4_q (SLit 1))) (SLit 255).
Lemma c4_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia | apply in_seq; lia].
Qed.
(* every atom holds z *)
Definition c4_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma c4_a0_val : forall E m, ew E 34 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E c4_a0 = Z_to_bv 64 (m mod 3).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (c4_envz m) c4_a0);
  [unfold c4_a0, c4_q; cbn [sv_denot ew c4_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (c4_all256 (fun z => bv_unsigned (sv_denot (c4_envz z) c4_a0) =? bv_unsigned (Z_to_bv 64 (z mod 3)))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.

(* ======================================== small helpers ======================================== *)
Lemma c4_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l H Hin. induction l as [|c l IH]; [exact Hin|]. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)]. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate H1.
Qed.
Lemma c4_nz : forall r : bv 5, (bv_unsigned r =? 0) = false -> bv_unsigned r <> 0.
Proof. intros r H. apply Z.eqb_neq. exact H. Qed.
Lemma c4_af : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof.
intros E n v lo hi al H Hv Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H, unsigned_lit_small by lia. auto.
Qed.
Lemma c4_u : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs extra) n) = v.
Proof. intros regs extra n r v Hn Hr Hv. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. apply unsigned_lit_small. lia. Qed.
(* byte k of a stored word is byte k of its low w bytes *)
Lemma c4_byte : forall v (w k : nat), (k < w)%nat -> (w <= 8)%nat ->
Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * Z.of_nat k)) = Z_to_bv 8 (YO0f.le_byte v w k).
Proof.
intros v w k Hk Hw. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). change 256 with (2 ^ 8).
rewrite Z.mod_mod by lia.
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hi8|Hi8].
- rewrite !(Z.mod_pow2_bits_low _ 8 i) by lia. rewrite !Z.shiftr_spec by lia.
  rewrite (Z.mod_pow2_bits_low v 64) by lia. rewrite (Z.mod_pow2_bits_low v (8 * Z.of_nat w)) by lia. reflexivity.
- rewrite !(Z.mod_pow2_bits_high _ 8 i) by lia. reflexivity.
Qed.
Lemma c4_val_of_chunk : forall E mem base off (n : N) e v,
YP09.chunk_ok rsegs E mem base (YP09.mkChunk off (CVal n e)) -> sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat ->
val_mem rsegs mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H He Hn k Hk. unfold YP09.chunk_ok in H.
cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
unfold YP09.byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal. apply c4_byte; lia.
Qed.
Lemma c4_nul0 : bv_unsigned NUL = 0.
Proof. unfold NUL. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma c4_map_zeros : forall n, map (fun x : byte => bv_unsigned x) (zeros n) = repeat 0 n.
Proof.
induction n as [|n IH]; [reflexivity|].
unfold zeros in *. cbn [repeat map]. rewrite IH, c4_nul0. reflexivity.
Qed.
(* the model's entry for case 4 (pod.h:326-330) *)
Lemma c4_model : forall (b : byte) (r : list byte), bv_unsigned b mod 10 = 4 ->
  ent_build (b :: r) = (Ent POD_BOOL 4 (le32 (fst (fuzz_u8 r) mod 3)), snd (fuzz_u8 r)).
Proof.
intros b r H. unfold ent_build. cbn [fuzz_u8]. rewrite H.
destruct r as [|x r']; reflexivity.
Qed.
Lemma c4_ent_mem : forall w, ent_mem (Ent POD_BOOL 4 (le32 w)) = le32 POD_BOOL ++ le32 4 ++ le32 w ++ zeros 92.
Proof.
intros w. unfold ent_mem. cbn [e_type e_size e_body]. rewrite length_le32. reflexivity.
Qed.

Ltac c4_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).
Ltac c4_b32 U := cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact U.
(* a register of the state after a run, as its symbolic value's denotation *)
Ltac c4_regv HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity);
    cbn [sv_denot]; rewrite ?ew_ewset_other by lia
  end.
Ltac c4_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; c4_kio].
Ltac c4_keptr K := rewrite K by first [apply c4_nz; reflexivity | apply c4_notin; reflexivity].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma c4_val_at : forall E ss (H : word -> bool) ms i r off (n : N) e v b a,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) -> base_val E (YP09.r_base r) = b ->
sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat -> a = b + off ->
val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss H ms i r off n e v b a HS Hi Hc Hb He Hn ->.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hi)).
pose proof (YP09.region_ok_chunk rsegs E _ r _ Hok Hc) as Hck. rewrite Hb in Hck.
exact (c4_val_of_chunk E _ b off n e v Hck He Hn).
Qed.

(* ---- the shadow entry over e: e is in scope and lies outside the shadow band ---- *)
Lemma c4_shok : forall (regs : bvmap 5 word) (H : word -> bool) mem (F vb m : Z),
  getr regs 18 = w64 SHADOW_OFF -> in_app F 512 ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0xf0) 104 ->
  sh_ok rsegs C4Bx c4_SH (Ereg regs (c4_extra F vb m)) (mrestrict H mem).
Proof.
intros regs H mem F vb m H18 Happ Hra.
set (E := Ereg regs (c4_extra F vb m)).
assert (U18 : U E (SOff 18 0) = SHADOW_OFF).
{ apply U_atom; [subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18 | unfold SHADOW_OFF; lia]. }
assert (U32 : U E (SOff 32 0) = F + 0xf0).
{ apply U_atom; [subst E; exact (ew_Ereg_extra regs _ 0)|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. pose proof alloc_ceiling_val. lia. }
apply Forall_cons; [|apply Forall_nil]. unfold shent_ok. cbn [she_m she_lo she_hi].
unfold C4Bx. rewrite U18, U32. split.
- rewrite <- (aview_rd_of rsegs). replace (F + 0xf0 + 0) with (F + 0xf0) by lia. exact Hra.
- unfold app_apart. cbn [she_m she_lo she_hi]. unfold C4Bx. rewrite U18, U32.
  intros a Ha. change (Z.min 0 0x68) with 0 in Ha. change (Z.max 0 0x68) with 0x68 in Ha.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. pose proof alloc_ceiling_val. lia.
Qed.

(* ---- the entry state ---- *)
Lemma c4_entry : forall (byte : bool) (W : world rsegs) (regs : bvmap 5 word) memc (R F c vb m nl : Z),
  getr regs 9 = w64 R -> getr regs 18 = w64 SHADOW_OFF -> getr regs 25 = w64 c -> getr regs 24 = w64 nl ->
  2 <= c -> c <= 2 ^ 47 - 1 -> 0 <= vb < 2 ^ 64 -> 0 <= m < 256 ->
  4096 <= F -> F + 512 <= alloc_ceiling -> alloc_ceiling <= R -> R + 0x1e0 <= 2 ^ 47 ->
  (byte = true -> 1 <= nl <= 2 ^ 47) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 vb ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) ->
  (forall o, 0 <= o < 12 -> apresent (w_H W) memc (F + 0xf0 + o)) ->
  (byte = true -> val_mem rsegs (mrestrict (w_H W) memc) c 1 m /\
     (c + 1 <= R + 0xe8 \/ R + 0xf0 <= c) /\ (c + 1 <= R + 0x138 \/ R + 0x140 <= c) /\
     (c + 1 <= F + 0xf0 \/ F + 0x158 <= c)) ->
  st_ok rsegs (Ereg regs (c4_extra F vb m)) (c4_ss byte)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D4) memc (seg_rom rsegs))).
Proof.
intros byte W regs memc R F c vb m nl H9 H18 H25 H24 Hc0 Hc1 Hvb Hm HF0 HFc HcR HR1 Hnl Ve8 V138 Pe Hbyte.
pose proof alloc_ceiling_val as Hac.
rewrite restrict_mkst_fx.
set (E := Ereg regs (c4_extra F vb m)).
assert (U9 : bv_unsigned (ew E 9) = R) by (exact (c4_u regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
assert (U25 : bv_unsigned (ew E 25) = c) by (exact (c4_u regs _ 25 25%bv c eq_refl H25 ltac:(lia))).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E25 : ew E 25 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E24 : ew E 24 = Z_to_bv 64 nl) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 (F + 0xf0)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 vb) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 m) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (U32 : bv_unsigned (ew E 32) = F + 0xf0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (RE : YP09.region_ok rsegs E (mrestrict (w_H W) memc) c4_rE).
{ unfold YP09.region_ok, c4_rE.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable rsegs). apply Pe. lia. }
assert (RA : YP09.region_ok rsegs E (mrestrict (w_H W) memc) c4_rA).
{ unfold YP09.region_ok, c4_rA.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ R 0xe8 8 (SOff 33 0) vb);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Ve8]. }
assert (RB : YP09.region_ok rsegs E (mrestrict (w_H W) memc) c4_rB).
{ unfold YP09.region_ok, c4_rB.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 32 0) (F + 0xf0));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V138]. }
unfold c4_ss. apply (entry_st_ok_full rsegs); try change (Ereg regs (c4_extra F vb m)) with E.
- apply regs_ok_Ereg.
- destruct byte; vm_compute; reflexivity.
- destruct byte; unfold c4_regs; repeat apply Forall_cons; try apply Forall_nil; try assumption.
  destruct (Hbyte eq_refl) as (Vb & _ & _ & _).
  unfold YP09.region_ok, c4_rI.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U25.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ c 0 1 (SOff 34 0) m);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Vb.
- destruct byte; unfold c4_regs, c4_rE, c4_rA, c4_rB, c4_rI;
    cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U25, ?U32.
  + destruct (Hbyte eq_refl) as (_ & D1 & D2 & D3). repeat split; first [exact I | lia].
  + repeat split; first [exact I | lia].
- unfold facts_ok. destruct byte; unfold c4_facts, c4_facts1, c4_facts0;
    cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  + split; [|split; exact I]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
    * apply (c4_af _ _ _ _ _ _ E18); unfold SHADOW_OFF;
        first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4_af _ _ _ _ _ _ E25); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4_af _ _ _ _ _ _ E32); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * pose proof (Hnl eq_refl) as Hnl'.
      apply (c4_af _ _ _ _ _ _ E24); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4_af _ _ _ _ _ _ E34); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
  + split; [|split; exact I]. split; [|split; [|split; [|exact I]]].
    * apply (c4_af _ _ _ _ _ _ E18); unfold SHADOW_OFF;
        first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4_af _ _ _ _ _ _ E25); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4_af _ _ _ _ _ _ E32); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ======================================== the block lemma ======================================== *)
Theorem w6b_c4 : w6b_c4_stmt B MT.
Proof using MTL.
unfold w6b_c4_stmt, w6b_case_stmt. cbv beta.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp b r Hctx HP Hin _.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & HRom).
unfold w6b_in in Hin.
destruct Hin as (Hr2 & Hr3 & Hr4 & H9 & H18 & H25 & H14 & H24 & H15 & H23 & H27 & H26 & H22 & M60 & Mb0 & Mc0
  & Me8 & M108 & M118 & M138 & Hvb & Hkd & Hpp0 & Hpp1 & HF0 & HFc & HF32 & HFapp & Hez & Hra
  & Hhull & Hc1 & Hwin & Hhull2 & Hdis2).
destruct Hwin as (Hg & Hrain & Hc0 & Hcb & Ham & Hdis).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof alloc_ceiling_val as Hac.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF32' & _ & HFpres & _).
rewrite <- HFa in HFpres.
change (fs_frame_bytes 3) with 512 in HFpres.
unfold T_SEG_STK, ASTACK in HspR.
assert (HcR : alloc_ceiling <= R) by lia.
assert (HR1 : R + 0x1e0 <= 2 ^ 47) by lia.
assert (Hpe : forall o, 0 <= o < 12 -> apresent (w_H W) memc (F + 0xf0 + o))
  by (intros o Ho; exact (proj1 (HFpres (F + 0xf0 + o) ltac:(lia)))).
assert (Hcmax : c + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
unfold cfg_at. change (w64 W6B_D4) with (Z_to_bv 64 W6B_D4).
destruct r as [|b1 r1].
- (* ============ no byte left: v = 0, 0x81994 .. J ============ *)
  pose proof (c4_entry false W regs memc R F c vb 0 _ H9 H18 H25 H24
    ltac:(lia) ltac:(cbn [length] in Hcmax; lia) Hvb ltac:(lia) HF0 HFc HcR HR1
    ltac:(discriminate) Me8 M138 Hpe ltac:(discriminate)) as HS0.
  pose proof (st_ok_pin_lit rsegs _ _ _ (24%bv : bv 5) 0 HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H24; reflexivity)) as HS.
  clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts c4_ss] in HS.
  assert (SHOK : sh_ok rsegs C4Bx c4_SH (Ereg regs (c4_extra F vb 0)) (mrestrict (w_H W) memc))
    by (apply (c4_shok regs (w_H W) memc F vb 0 H18 HFapp Hra)).
  assert (HAE : env_agree 32 (Ereg regs (c4_extra F vb 0)) (Ereg regs (c4_extra F vb 0)))
    by apply env_agree_refl.
  assert (E32 : ew (Ereg regs (c4_extra F vb 0)) 32 = Z_to_bv 64 (F + 0xf0)) by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (c4_extra F vb 0)) 33 = Z_to_bv 64 vb) by exact (ew_Ereg_extra regs _ 1).
  assert (U32 : bv_unsigned (ew (Ereg regs (c4_extra F vb 0)) 32) = F + 0xf0)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (Ereg regs (c4_extra F vb 0)) 9) = R)
    by (exact (c4_u regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (U25 : bv_unsigned (ew (Ereg regs (c4_extra F vb 0)) 25) = c)
    by (exact (c4_u regs _ 25 25%bv c eq_refl H25 ltac:(lia))).
  aj_run_to_tok w6_tbl_ok HS HJ SHOK C4span W6_J.
  + (* the write rights of e *)
    lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ow) end.
    eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0xf0);
      [ reflexivity | rewrite <- HFa; exact U32 | exact Hown
      | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    awr_ok_tac.
  + (* the leaf at J *)
    assert (KEEPR : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [10; 11; 12; 22; 24]%bv ->
      getr (ms_regs ms) rr = getr regs rr)
      by (eapply (regs_kept_of_st_ok rsegs _ _ ms regs (c4_extra F vb 0) (w_H W) _ HS);
          [env_agree_chain HAE | vm_compute; reflexivity]).
    assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xf0 <= a < F + 0xfc) ->
      mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) a = mbyte rsegs (mrestrict (w_H W) memc) a).
    { intros a Ha Hn. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
      intros (rg & Hin & Hr). apply Hn. rewrite unsigned_lit_small in Hr by lia.
      cbn [ss_mem c4_ss c4_regs In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c4_rE c4_rA c4_rB] in Hr;
        rewrite ?U9, ?U32 in Hr; lia. }
    apply SRr_ret. red.
    exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
    split; [exact HJ|].
    split; [intros rr Hr0 Hn; apply KEEPR; [exact Hr0|];
            intros X; apply Hn; unfold w6b_clob; cbn [In] in X |- *; tauto|].
    split; [reflexivity|].
    split; [apply Permutation_refl|].
    split; [c4_kio|].
    split; [apply mo_le_refl; exact MTL|].
    split; [intros a Ha Hn; unfold aview;
            rewrite (KEEPB a Ha ltac:(intros X; apply Hn; unfold w6b_wr; right; right; lia)); reflexivity|].
    unfold w6b_J_R. rewrite (c4_model b (@nil byte) HP). cbn [fst snd fuzz_u8].
    split; [c4_regv HS (22%bv : bv 5); rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [c4_keptr KEEPR; exact H23|].
    split; [c4_keptr KEEPR; exact H26|].
    split; [c4_keptr KEEPR; exact H27|].
    split; [c4_regv HS (25%bv : bv 5); rewrite U25; unfold w64; f_equal; cbn [length]; lia|].
    split; [c4_regv HS (24%bv : bv 5); unfold w64; f_equal; cbn [length]; lia|].
    (* e's 104 bytes *)
    assert (V0 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf0) 4 POD_BOOL)
      by (eapply (c4_val_at _ _ (w_H W) ms 0%nat _ 0 4%N (SLit 2) POD_BOOL (F + 0xf0) _);
          [exact HS | reflexivity | c4_in | c4_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (V4 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf4) 4 4)
      by (eapply (c4_val_at _ _ (w_H W) ms 0%nat _ 4 4%N (SLit 4) 4 (F + 0xf0) _);
          [exact HS | reflexivity | c4_in | c4_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (V8 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf8) 4 (0 mod 3))
      by (eapply (c4_val_at _ _ (w_H W) ms 0%nat _ 8 4%N (SLit 0) (0 mod 3) (F + 0xf0) _);
          [exact HS | reflexivity | c4_in | c4_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (VZ : garr8 rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xfc) (repeat 0 92)).
    { apply garr8_zeros. intros a Ha. cbn [Z.of_nat] in Ha.
      rewrite (KEEPB a ltac:(lia) ltac:(lia)).
      replace a with (F + 0xf0 + (a - (F + 0xf0))) by lia. apply Hez. lia. }
    rewrite c4_ent_mem, !map_app, c4_map_zeros.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RtPgMem.rtm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0xf0) 4%nat POD_BOOL V0)|].
    rewrite length_map, length_le32. replace (F + 0xf0 + Z.of_nat 4) with (F + 0xf4) by lia.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RtPgMem.rtm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0xf4) 4%nat 4 V4)|].
    rewrite length_map, length_le32. replace (F + 0xf4 + Z.of_nat 4) with (F + 0xf8) by lia.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RtPgMem.rtm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0xf8) 4%nat (0 mod 3) V8)|].
    rewrite length_map, length_le32. replace (F + 0xf8 + Z.of_nat 4) with (F + 0xfc) by lia.
    exact VZ.
- (* ============ a byte: v = b1, 0x81668 .. J ============ *)
  pose proof (Cursor.byte_range b1) as Hmb.
  assert (HD : (c + 1 <= R + 0xe8 \/ R + 0xf0 <= c) /\ (c + 1 <= R + 0x138 \/ R + 0x140 <= c))
    by (pose proof (Hdis c ltac:(cbn [length]; lia)) as Hq; destruct Hq as (Hq1 & Hq2 & Hq3); lia).
  assert (HDF : c + 1 <= F + 0xf0 \/ F + 0x158 <= c)
    by (pose proof (Hdis2 c ltac:(cbn [length]; lia)); lia).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) c 1 (bv_unsigned b1))
    by (destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]; rewrite Z.add_0_r in Hv; exact Hv).
  pose proof (c4_entry true W regs memc R F c vb (bv_unsigned b1) _ H9 H18 H25 H24
    ltac:(lia) ltac:(cbn [length] in Hcmax; lia) Hvb Hmb HF0 HFc HcR HR1
    ltac:(intros _; cbn [length] in Hcmax |- *; lia) Me8 M138 Hpe
    ltac:(intros _; split; [exact Hm0|]; split; [exact (proj1 HD)|];
          split; [exact (proj2 HD) | exact HDF])) as HS.
  assert (SHOK : sh_ok rsegs C4Bx c4_SH (Ereg regs (c4_extra F vb (bv_unsigned b1))) (mrestrict (w_H W) memc))
    by (apply (c4_shok regs (w_H W) memc F vb (bv_unsigned b1) H18 HFapp Hra)).
  assert (HAE : env_agree 32 (Ereg regs (c4_extra F vb (bv_unsigned b1)))
                  (Ereg regs (c4_extra F vb (bv_unsigned b1)))) by apply env_agree_refl.
  assert (E14 : ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 14 = Z_to_bv 64 (c - 1))
    by (rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
  assert (E15 : ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 15
                  = Z_to_bv 64 (Z.of_nat (length (b1 :: r1)) + 1))
    by (rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
  assert (E18 : ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 18 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E25 : ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 25 = Z_to_bv 64 c)
    by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
  assert (E32 : ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 32 = Z_to_bv 64 (F + 0xf0))
    by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 33 = Z_to_bv 64 vb)
    by exact (ew_Ereg_extra regs _ 1).
  assert (E34 : ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 34 = Z_to_bv 64 (bv_unsigned b1))
    by exact (ew_Ereg_extra regs _ 2).
  assert (U32 : bv_unsigned (ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 32) = F + 0xf0)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 9) = R)
    by (exact (c4_u regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (U25 : bv_unsigned (ew (Ereg regs (c4_extra F vb (bv_unsigned b1))) 25) = c)
    by (exact (c4_u regs _ 25 25%bv c eq_refl H25 ltac:(lia))).
  aj_run_to_tok w6_tbl_ok HS HJ SHOK C4span W6_J.
  + (* the check's obligation: the input byte is addressable *)
    apply (obl_of_range rsegs (w_H W) memc _ C4Bx _ _ c (Z.of_nat (length (b1 :: r1))) Hrain).
    * exact (U_atom _ 18 SHADOW_OFF E18 ltac:(unfold SHADOW_OFF; lia)).
    * rewrite (U_atom _ 25 c E25 ltac:(lia)). lia.
    * rewrite (U_atom _ 25 c E25 ltac:(lia)). cbn [length]. lia.
  + (* the write rights of e *)
    lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ow) end.
    eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0xf0);
      [ reflexivity | rewrite <- HFa; exact U32 | exact Hown
      | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    awr_ok_tac.
  + (* the leaf at J *)
    assert (KEEPR : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [10; 11; 12; 22; 24; 25]%bv ->
      getr (ms_regs ms) rr = getr regs rr)
      by (eapply (regs_kept_of_st_ok rsegs _ _ ms regs (c4_extra F vb (bv_unsigned b1)) (w_H W) _ HS);
          [env_agree_chain HAE | vm_compute; reflexivity]).
    assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xf0 <= a < F + 0xfc) ->
      mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) a = mbyte rsegs (mrestrict (w_H W) memc) a).
    { intros a Ha Hn. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
      intros (rg & Hin & Hr). apply Hn. rewrite unsigned_lit_small in Hr by lia.
      cbn [ss_mem c4_ss c4_regs In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c4_rE c4_rA c4_rB c4_rI] in Hr;
        rewrite ?U9, ?U25, ?U32 in Hr; lia. }
    apply SRr_ret. red.
    exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
    split; [exact HJ|].
    split; [intros rr Hr0 Hn; apply KEEPR; [exact Hr0|];
            intros X; apply Hn; unfold w6b_clob; cbn [In] in X |- *; tauto|].
    split; [reflexivity|].
    split; [apply Permutation_refl|].
    split; [c4_kio|].
    split; [apply mo_le_refl; exact MTL|].
    split; [intros a Ha Hn; unfold aview;
            rewrite (KEEPB a Ha ltac:(intros X; apply Hn; unfold w6b_wr; right; right; lia)); reflexivity|].
    unfold w6b_J_R. rewrite (c4_model b (b1 :: r1) HP). cbn [fst snd fuzz_u8].
    split; [c4_regv HS (22%bv : bv 5); rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [c4_keptr KEEPR; exact H23|].
    split; [c4_keptr KEEPR; exact H26|].
    split; [c4_keptr KEEPR; exact H27|].
    split; [c4_regv HS (25%bv : bv 5); rewrite E14, unsigned_lit_small by lia;
            unfold w64; f_equal; cbn [length]; lia|].
    split; [c4_regv HS (24%bv : bv 5); rewrite E15, unsigned_lit_small by (cbn [length] in Hcmax |- *; lia);
            unfold w64; f_equal; cbn [length]; lia|].
    (* e's 104 bytes *)
    assert (V0 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf0) 4 POD_BOOL)
      by (eapply (c4_val_at _ _ (w_H W) ms 0%nat _ 0 4%N (SLit 2) POD_BOOL (F + 0xf0) _);
          [exact HS | reflexivity | c4_in | c4_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (V4 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf4) 4 4)
      by (eapply (c4_val_at _ _ (w_H W) ms 0%nat _ 4 4%N (SLit 4) 4 (F + 0xf0) _);
          [exact HS | reflexivity | c4_in | c4_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (V8 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf8) 4 (bv_unsigned b1 mod 3)).
    { eapply (c4_val_at _ _ (w_H W) ms 0%nat _ 8 4%N c4_a0 (bv_unsigned b1 mod 3) (F + 0xf0) _);
      [exact HS | reflexivity | c4_in | c4_b32 U32 | | cbn; lia | lia].
      apply c4_a0_val; [rewrite ?ew_ewset_other by lia; exact E34 | exact Hmb]. }
    assert (VZ : garr8 rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xfc) (repeat 0 92)).
    { apply garr8_zeros. intros a Ha. cbn [Z.of_nat] in Ha.
      rewrite (KEEPB a ltac:(lia) ltac:(lia)).
      replace a with (F + 0xf0 + (a - (F + 0xf0))) by lia. apply Hez. lia. }
    rewrite c4_ent_mem, !map_app, c4_map_zeros.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RtPgMem.rtm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0xf0) 4%nat POD_BOOL V0)|].
    rewrite length_map, length_le32. replace (F + 0xf0 + Z.of_nat 4) with (F + 0xf4) by lia.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RtPgMem.rtm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0xf4) 4%nat 4 V4)|].
    rewrite length_map, length_le32. replace (F + 0xf4 + Z.of_nat 4) with (F + 0xf8) by lia.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RtPgMem.rtm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0xf8) 4%nat
                (bv_unsigned b1 mod 3) V8)|].
    rewrite length_map, length_le32. replace (F + 0xf8 + Z.of_nat 4) with (F + 0xfc) by lia.
    exact VZ.
Qed.

End d.
End b.

Print Assumptions w6b_c4.
