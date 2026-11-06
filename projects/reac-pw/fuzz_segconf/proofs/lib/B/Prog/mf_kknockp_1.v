(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 494 of its 542 lines of code are new or changed and 405 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_kknock.v, with its module paths, module names and numbers changed; 222 of its 327 lines of code are new or changed and 437 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): segment S_MF_KKNOCKP (KKNOCK 0x86a7c ->
   KDONE 0x86c1c) of lib/B/Prog/m_file_m.v, part 1: its inner cut statements, the model and byte-encoding facts its
   walk uses, and the facts its walk takes from the shared step files. A walk lane of the image-B m_file-family owner's G2B.
   proves no function (kind: segment statements and pure facts of m_file's image-B walk).

   THE CODE (the neutral listing of m_file in image B, the image-B m_file cut map section 4 S_MF_KKNOCKP):
     0x86a7c  ld a0,208(s1) (k); auipc/addi a2 = "knock" (listing object 25, 0x212e0); mv a1,s5 (kl)
     0x86a8c  jal ieq                                         -> KK_R1 0x86a90
     0x86a90  beqz a0 -> 0x86c0c (a key other than "knock")
     0x86c0c  mv a0,s9 (c); mv a1,s11 (line + 1); 0x86c14 jal m_refuse (knock = false) -> 0x86c18 li s4,511 -> KDONE
     0x86a94  ld a0,48(s1) (c + 0x23ac = &n_kept); the instrumented check 0x86aa0 of the 4-byte load (a load of the
              shadow byte at (a0 >> 3) + s2 and a compare; slow path 0x86cf0-0x86cfc; the error path 0x86f20, a call
              of errpath_load4, which the proof shows is not reached); li s4,511; lw a0,0(a0) (n_kept)
     0x86ab4  blt 7,n_kept -> 0x86af4 (n_kept = 8: no store)
     0x86abc  bltu 7,n_kept -> the UBSan trap 0x86e84 (not taken: 0 <= n_kept, mconf_encp's u32 n_kept)
     0x86ac8  bltu ~(c + 0x238c),4 n_kept -> the trap 0x86e84 (not taken: 40(s1) = ~(c + 0x238c), c + 9236 <= 2^64)
     0x86adc  the check of the 4-byte store at c + 0x238c + 4 n_kept (slow path 0x86d48-0x86d54; the error path
              0x86f3c, errpath_store4, not reached); sw 1 there (kept_knock[n_kept] = 1); ld s9,112(s1); li s4,511
     0x86af4  mv a0,s9; mv a1,s11; 0x86afc jal m_refuse (knock = true) -> 0x86b00 j KDONE
   INNER CUTS: KK_R1 0x86a90 (ieq "knock" returned, a0 = b2z b), the two m_refuse calls KK_RMISS 0x86c14 / KK_RHIT
   0x86afc and their returns KK_AMISS 0x86c18 / KK_AHIT 0x86b00 (KK_AF_stmt: the line refused, on to KDONE).
   THE MODEL: with "role", "model", "ignore" missed, mk_disp is m_refuse mcc (line + 1) (ieq k S_knock) (kk_disp).
   THE KNOCK STORE: kept_knock[n_kept] = 1 for n_kept < 8 turns mconf_encp false into mconf_encp true (kk_encp_store);
   n_kept = 8 has no pending slot, so false and true are the same encoding (kk_encp8).
   SHARED STEPS (the image-B m_file-family owner's decision, 18:2xZ): the keep lemmas, the knock-state core mf_corek and mf_loop_next are
   lib/B/Prog/m_file_k.v's (84ea19e46fcc); ieq's call is lib/B/Prog/m_file_iq.v's mf_ieq_call
   (c02ea38a1d41); m_refuse's call is lib/B/Prog/m_file_rf.v's mf_refuse_step (edc599bcca5a). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegPgBase SegBase SegObj SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_refuse_c m_file_m m_file_mdl m_file_sd m_file_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the inner cuts ===================================== *)
Definition KK_R1 : Z := AF_m_file + 0x950.     (* 0x86a90, ieq "knock" returned *)
Definition KK_RMISS : Z := AF_m_file + 0xad4.  (* 0x86c14, jal m_refuse (a key other than "knock") *)
Definition KK_AMISS : Z := AF_m_file + 0xad8.  (* 0x86c18, its return: li s4,511 *)
Definition KK_RHIT : Z := AF_m_file + 0x9bc.   (* 0x86afc, jal m_refuse (the knock line) *)
Definition KK_AHIT : Z := AF_m_file + 0x9c0.   (* 0x86b00, its return: j KDONE *)

(* ===================================== the model ===================================== *)
(* the key missed "role", "model" and "ignore": m_key refuses the line, with the knock flag ieq k "knock" *)
Lemma kk_disp : forall c gi k v L, ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = false ->
  mk_disp c gi k v L = m_refuse c L (ieq k S_knock).
Proof. intros c gi k v L H1 H2 H3. unfold mk_disp. rewrite H1, H2, H3. destruct (ieq k S_knock); reflexivity. Qed.
Lemma kk_disp_miss : forall c gi k v L, Forall (fun w => ieq k w = false) [S_role; S_model; S_ignore] ->
  mk_disp c gi k v L = m_refuse c L (ieq k S_knock).
Proof.
intros c gi k v L HM. apply Forall_cons_iff in HM as [H1 HM]. apply Forall_cons_iff in HM as [H2 HM].
apply Forall_cons_iff in HM as [H3 _]. exact (kk_disp c gi k v L H1 H2 H3).
Qed.
(* what m_refuse changes of the counters *)
Lemma kk_refuse_cnt : forall c l k,
  mc_refused (m_refuse c l k) = mc_refused c + 1 /\ mc_overflow (m_refuse c l k) = mc_overflow c /\
  (length (mc_kept c) <= length (mc_kept (m_refuse c l k)))%nat.
Proof.
intros c l k. destruct (m_refuse_sizes c l k) as [_ HK]. unfold m_refuse at 1 2. cbv zeta. cbn [mc_refused mc_overflow].
split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.
(* the refusal of a line with fewer than 8 kept refusals keeps one more *)
Lemma kk_refuse_kept : forall c l k, (length (mc_kept c) < 8)%nat ->
  length (mc_kept (m_refuse c l k)) = S (length (mc_kept c)).
Proof.
intros c l k H. unfold m_refuse. cbv zeta. cbn [mc_kept].
destruct (Z.ltb_spec (Z.of_nat (length (mc_kept c))) 8) as [_|C]; [|exfalso; lia].
rewrite length_app. cbn [length]. lia.
Qed.

(* the line is a prefix of the text left *)
Lemma kk_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
intros rest. unfold mf_line. induction rest as [|b r IH]; [cbn; lia|]. cbn [break_nl].
destruct (b =? NL); [cbn [fst length]; lia|].
destruct (break_nl r) as [l q]. cbn [fst length] in *. lia.
Qed.

(* ===================================== the text's bytes ===================================== *)
(* image A's lib/A/Prog/m_file_s_kign_t.v (a working branch) ki_aview_byte, ki_zs_zb, ki_bytes_of_zs,
   restated: ieq_pre's bytes, the list Z read through an ASan reader as list byte, and back *)
Lemma kk_aview_byte : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
intros segs H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; [|discriminate]. cbn in E. injection E as <-.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.
Lemma kk_zs_zb : forall l, Forall (fun z => 0 <= z < 256) l -> seg_spec.zs (seg_spec.zb l) = l.
Proof.
induction l as [|x r IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [Hx Hr].
unfold seg_spec.zs, seg_spec.zb in *. cbn [map]. rewrite IH by exact Hr. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hx.
Qed.
Lemma kk_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
  sa_bytes (aview segs H mem) a (seg_spec.zb l) /\ seg_spec.zs (seg_spec.zb l) = l /\
  Forall (fun z => 0 <= z < 256) l.
Proof.
intros segs H mem a l HZ.
assert (HR : Forall (fun z => 0 <= z < 256) l).
{ apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (i & Hi & <-).
  exact (kk_aview_byte segs H mem _ _ (HZ i Hi)). }
split; [|split; [exact (kk_zs_zb l HR) | exact HR]].
intros i Hi. unfold seg_spec.zb in Hi. rewrite length_map in Hi. rewrite (HZ i Hi). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.

(* ===================================== the block's bytes ===================================== *)
(* image A's lib/A/Prog/m_file_s_hdrb_1.v (a working branch) mcx_nth_ext, mcx_fld_nth, mcx_fld_length,
   mcx_fld_upd_out, mcx_fld_upd_same, hb_nth_le_bytes, hb_le4_byte, hb_nth_fld, hb_nth_of_error, hb_val_of_u32,
   hb_bytes_upd, hb_bytes_of_val, restated *)
Lemma kk_nth_ext : forall {A} (l l' : list A), (forall i, nth_error l i = nth_error l' i) -> l = l'.
Proof.
  intros A l. induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - pose proof (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.
Lemma kk_fld_nth : forall off n (L : list byte) i,
  nth_error (seg_spec.fld off n L) i = if (i <? n)%nat then nth_error L (off + i) else None.
Proof.
  intros off n L i. unfold seg_spec.fld. rewrite nth_error_firstn.
  destruct (i <? n)%nat; [|reflexivity]. rewrite nth_error_skipn. f_equal; lia.
Qed.
Lemma kk_fld_upd_out : forall (L : list byte) k nb off n, (k + length nb <= length L)%nat ->
  (off + n <= k \/ k + length nb <= off)%nat -> seg_spec.fld off n (upd_bytes L k nb) = seg_spec.fld off n L.
Proof.
  intros L k nb off n H1 H2. apply kk_nth_ext. intros i. rewrite !kk_fld_nth.
  destruct (Nat.ltb_spec0 i n) as [Hi|Hi]; [|reflexivity].
  destruct (Nat.ltb_spec0 (off + i) (length L)) as [Hl|Hl].
  - rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (off + i)); destruct (Nat.ltb_spec0 (off + i) (k + length nb)); cbn [andb];
      first [reflexivity | exfalso; lia].
  - rewrite (proj2 (nth_error_None L (off + i))) by lia.
    apply nth_error_None. rewrite upd_bytes_length by lia. lia.
Qed.
Lemma kk_fld_upd_same : forall (L : list byte) k n nb, n = length nb -> (k + n <= length L)%nat ->
  seg_spec.fld k n (upd_bytes L k nb) = nb.
Proof.
  intros L k n nb -> H. apply kk_nth_ext. intros i. rewrite kk_fld_nth.
  destruct (Nat.ltb_spec0 i (length nb)) as [Hi|Hi].
  - rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (k + i)); destruct (Nat.ltb_spec0 (k + i) (k + length nb)); cbn [andb];
      first [f_equal; lia | exfalso; lia].
  - symmetry. apply nth_error_None. lia.
Qed.
Lemma kk_nth_le_bytes : forall n z k, (k < n)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes n z) ZB0) = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
  induction n as [|n IH]; intros z k Hk; [exfalso; lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth].
  - rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 2 ^ 8).
    replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma kk_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold le4, le_byte.
  rewrite kk_nth_le_bytes by exact Hk.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity.
  rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.
Lemma kk_nth_fld : forall off n (L : list byte) i d, (i < n)%nat -> (off + n <= length L)%nat ->
  nth i (seg_spec.fld off n L) d = nth (off + i) L d.
Proof.
  intros off n L i d Hi HL. apply nth_error_nth. rewrite kk_fld_nth.
  destruct (Nat.ltb_spec0 i n) as [_|C]; [|exfalso; lia].
  apply nth_error_nth'. lia.
Qed.
Lemma kk_nth_of_error : forall (L L' : list byte) i j d, nth_error L i = nth_error L' j -> (j < length L')%nat ->
  nth i L d = nth j L' d.
Proof. intros L L' i j d E H. apply nth_error_nth. rewrite E. apply nth_error_nth'. exact H. Qed.
(* a u32 field of a block read through the reader *)
Lemma kk_val_of_u32 : forall rd c bs off v, sa_bytes rd c bs -> (off + 4 <= length bs)%nat ->
  seg_spec.u32_enc v (seg_spec.fld off 4 bs) -> sa_val rd (c + Z.of_nat off) 4 v.
Proof.
  intros rd c bs off v Hb HL [Hv Hf]. unfold sa_bytes, sa_val in *. intros k Hk.
  replace (c + Z.of_nat off + Z.of_nat k) with (c + Z.of_nat (off + k)) by lia.
  rewrite (Hb (off + k)%nat) by lia. f_equal.
  rewrite <- (kk_nth_fld off 4 bs k ZB0) by lia. rewrite Hf. apply kk_le4_byte; [exact Hv | exact Hk].
Qed.
(* the block after a write whose part inside it is X at offset k *)
Lemma kk_bytes_upd : forall rd rd' c BS k X, sa_bytes rd c BS -> sa_bytes rd' (c + Z.of_nat k) X ->
  (k + length X <= length BS)%nat ->
  (forall a, c <= a < c + Z.of_nat (length BS) ->
     ~ (c + Z.of_nat k <= a < c + Z.of_nat k + Z.of_nat (length X)) -> rd' a = rd a) ->
  sa_bytes rd' c (upd_bytes BS k X).
Proof.
  intros rd rd' c BS k X HB HX HL HK. unfold sa_bytes in *. intros i Hi.
  rewrite upd_bytes_length in Hi by exact HL.
  pose proof (upd_bytes_nth BS k X i HL Hi) as E. revert E.
  destruct (Nat.leb_spec0 k i) as [H1|H1]; destruct (Nat.ltb_spec0 i (k + length X)) as [H2|H2];
    cbn [andb]; intros E.
  1: { rewrite (kk_nth_of_error _ X i (i - k) ZB0 E) by lia.
       replace (c + Z.of_nat i) with (c + Z.of_nat k + Z.of_nat (i - k)) by lia.
       apply HX. lia. }
  all: rewrite (kk_nth_of_error _ BS i i ZB0 E) by lia; rewrite HK by lia; apply HB; exact Hi.
Qed.
(* a 4-byte value read through the reader is the bytes le4 *)
Lemma kk_bytes_of_val : forall rd a v, 0 <= v < 2 ^ 32 -> sa_val rd a 4 v -> sa_bytes rd a (le4 (Z_to_bv 64 v)).
Proof.
  intros rd a v Hv HV. unfold sa_val, sa_bytes in *. intros i Hi. rewrite length_le4 in Hi.
  rewrite HV by exact Hi. f_equal. symmetry. apply kk_le4_byte; assumption.
Qed.

Ltac kk_lia := unfold seg_spec.MC_N, seg_spec.MC_OVERFLOW, seg_spec.MC_REFUSED, seg_spec.MC_KEPT, seg_spec.MC_KNOCK,
  seg_spec.MC_NKEPT, seg_spec.MC_GEN, seg_spec.MC_READING, seg_spec.SEG_M_SIZE in *; lia.
Ltac kk_keep H := rewrite kk_fld_upd_out by kk_lia; exact H.

(* n_kept of an encoded block (the load at c + 0x23ac) and its bounds *)
Lemma kk_nkept_val : forall pend rd c mc, sa_mconfp pend rd c mc ->
  sa_val rd (c + seg_spec.MC_NKEPT) 4 (Z.of_nat (length (mc_kept mc))) /\ (length (mc_kept mc) <= 8)%nat.
Proof.
intros pend rd c mc (bs & Hb & He). pose proof He as (H1 & _ & _ & _ & _ & _ & H7 & _ & _ & H10 & _).
split; [|exact H7].
unfold seg_spec.fldz in H10.
replace (c + seg_spec.MC_NKEPT) with (c + Z.of_nat (Z.to_nat seg_spec.MC_NKEPT)) by (unfold seg_spec.MC_NKEPT; lia).
apply (kk_val_of_u32 rd c bs); [exact Hb | kk_lia | exact H10].
Qed.
(* n_kept = 8: no pending slot, the two encodings agree *)
Lemma kk_encp8 : forall mc bs, length (mc_kept mc) = 8%nat ->
  seg_spec.mconf_encp false mc bs -> seg_spec.mconf_encp true mc bs.
Proof.
intros mc bs H8 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & HK & H9 & H10 & H11 & H12).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj HK (conj _ (conj H10 (conj H11 H12))))))))))).
intros i Hi. lia.
Qed.
(* n_kept < 8: kept_knock[n_kept] = 1 makes the pending flag true *)
Lemma kk_encp_store : forall mc bs, (length (mc_kept mc) < 8)%nat -> seg_spec.mconf_encp false mc bs ->
  seg_spec.mconf_encp true mc
    (upd_bytes bs (Z.to_nat seg_spec.MC_KNOCK + 4 * length (mc_kept mc)) (le4 (Z_to_bv 64 1))).
Proof.
intros mc bs Hn (H1 & H2 & H3 & H4 & H5 & H6 & H7 & HK & H9 & H10 & H11 & H12).
pose proof (length_le4 (Z_to_bv 64 1)) as Hl4.
assert (HL : length bs = 9236%nat) by (apply Nat2Z.inj; rewrite H1; reflexivity).
unfold seg_spec.mconf_encp, seg_spec.fldz in *.
split; [rewrite upd_bytes_length by kk_lia; exact H1|].
split; [exact H2|].
split; [intros i Hi; pose proof (H3 i Hi) as Hs; rewrite kk_fld_upd_out by kk_lia; exact Hs|].
split; [kk_keep H4|]. split; [kk_keep H5|]. split; [kk_keep H6|].
split; [exact H7|].
split.
{ intros i Hi. destruct (HK i Hi) as [Ha Hb].
  split; [kk_keep Ha | kk_keep Hb]. }
split.
{ intros i Hi. destruct (Nat.eq_dec i (length (mc_kept mc))) as [->|Hne].
  - rewrite kk_fld_upd_same by kk_lia. rewrite Nat.eqb_refl. reflexivity.
  - rewrite kk_fld_upd_out by kk_lia. pose proof (H9 i Hi) as Hf.
    replace (true && (i =? length (mc_kept mc)))%nat with (false && (i =? length (mc_kept mc)))%nat
      by (rewrite (proj2 (Nat.eqb_neq _ _) Hne); reflexivity).
    exact Hf. }
split; [kk_keep H10|]. split; [kk_keep H11|].
kk_keep H12.
Qed.
(* kept_knock[n_kept], for n_kept below the final model's kept count, is in m_file's footprint *)
Lemma kk_fp_knock : forall c k0 mcf (n : nat) a, (k0 <= n)%nat -> (n < length (mc_kept mcf))%nat ->
  c + seg_spec.MC_KNOCK + 4 * Z.of_nat n <= a < c + seg_spec.MC_KNOCK + 4 * Z.of_nat n + 4 ->
  inFP (M_FILE_FP c k0 mcf) a.
Proof.
intros c k0 mcf n a H0 H1 Ha. unfold M_FILE_FP.
do 3 (apply inFP_cons; right). apply inFP_cons. left. cbn [fst snd]. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom (image A's m_file_s_kign_1.v ki_st_reg) *)
Lemma kk_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros segs E ss H ms r n HS Hr. rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the callee-saved registers of a state whose symbolic registers are the seed's on CALLEE_SAVED (image A's
   ki_pres) *)
Lemma kk_pres : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word),
  E = mfE regs1 v lyc pos cur np xs -> mf_regs_base v regs1 ->
  (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get R r) (sr_get sr_mf r)) CALLEE_SAVED = true ->
  aregs_preserved regs1 rr.
Proof.
intros E R regs1 v lyc pos cur np xs rr HE RB HR HC r Hr.
pose proof (mf_regs_ok v regs1 lyc pos cur np xs RB) as HO. rewrite <- HE in HO.
rewrite HR, HO. f_equal. apply sv_eqb_eq.
assert (Hin : In (Z_to_bv 5 r) CALLEE_SAVED).
{ unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    unfold CALLEE_SAVED; cbn [In]; first [ tauto | intuition (apply bv_eq; reflexivity) ]. }
exact (proj1 (forallb_forall _ _) HC _ Hin).
Qed.

(* the text left's sub-range [o, o + n) inside it: its bytes as list byte, addressable, in the text block (image
   A's ki_slice_facts) *)
Lemma kk_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc cur line p rest ->
  (o + n <= length rest)%nat ->
  sa_bytes (rdW Wc memc) (p + Z.of_nat o) (seg_spec.zb (firstn n (skipn o rest))) /\
  seg_spec.zs (seg_spec.zb (firstn n (skipn o rest))) = firstn n (skipn o rest) /\
  Z.of_nat (length (seg_spec.zb (firstn n (skipn o rest)))) = Z.of_nat n /\
  sa_addr (rdW Wc memc) (p + Z.of_nat o) (Z.of_nat n) /\ sa_heap B lyc Sc (p + Z.of_nat o) (Z.of_nat n) /\
  p + Z.of_nat o <> 0.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n CX CORE LOOP Hon.
pose proof LOOP as (L1 & L2 & L3 & ((LZ & LN) & LT) & LADDR & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
assert (HZ : sa_zs (rdW Wc memc) (p + Z.of_nat o) (firstn n (skipn o rest))).
{ intros i Hi. rewrite length_firstn, length_skipn in Hi.
  replace (p + Z.of_nat o + Z.of_nat i) with (p + Z.of_nat (o + i)) by lia.
  rewrite (LZ (o + i)%nat) by (rewrite length_app; cbn [length]; lia).
  f_equal. rewrite nth_firstn. destruct (Nat.ltb_spec i n) as [Hlt|Hge]; [|lia].
  rewrite nth_skipn. apply app_nth1. lia. }
destruct (kk_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HZB & _).
destruct (mf_txt_heap_now B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bt & mt & Hin & Hb & He).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hin) as (_ & Hbt4096 & Hbtceil & _ & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrt].
assert (Hlen : length (seg_spec.zb (firstn n (skipn o rest))) = n).
{ unfold seg_spec.zb. rewrite length_map, length_firstn, length_skipn. lia. }
pose proof LADDR as (A0 & A1 & AM & ARA & AHV).
assert (Hpe : p + Z.of_nat (length rest) <= mv_t v + Z.of_nat (length (mv_s v))) by (rewrite L3; lia).
assert (Hpt : mv_t v <= p) by (rewrite L3; lia).
split; [exact HB|]. split; [exact HZB|]. split; [rewrite Hlen; reflexivity|]. split.
- split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  + exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR Hin
      ltac:(lia) ltac:(lia)).
  + intros Hn. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR
      Hin ltac:(lia) ltac:(lia) Hn).
- split; [exists bt, mt; split; [exact Hin | lia] | lia].
Qed.

(* 0x86a90, ieq "knock" returned with a0 = b2z b: the key k missed "role", "model", "ignore", and b = ieq k "knock";
   the model refuses the line with the knock flag b. s11 = line + 1, 152(s1) = the next line's address, low.i in
   scope; the key and the value are no longer read *)
Definition KK_R1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (b : bool),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mf_fin (m_refuse mcc (line + 1) b, Some gi) line rest = mf_final v ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
getr regs1 10 = w64 (seg_spec.b2z b) ->
mf_at B v Wc regs1 memc mdc KK_R1.

(* 0x86c18 / 0x86b00, m_refuse returned: the block holds the refused model, the line loop's facts are still the line
   head's; s4 = 511 already at 0x86b00 (set at 0x86aa4 / 0x86af0), set by 0x86c18 itself on the other path *)
Definition KK_AF_stmt (pc : Z) (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (b : bool),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON (m_refuse mcc (line + 1) b) -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mf_fin (m_refuse mcc (line + 1) b, Some gi) line rest = mf_final v ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
(pc = KK_AHIT -> getr regs1 20 = w64 511) ->
mf_at B v Wc regs1 memc mdc pc.
End e.
End f.
End d.
