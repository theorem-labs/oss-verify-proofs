(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PutStringB_Base.v, with its module paths and module names changed; 941 of its 1032 lines of code are new or changed and 1922 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the TRIM CALL and the R5 EXITS of segment A5 of
   reac_segconf_parse_file's walk (2026-10-30).

   Two pieces of lib/A/Prog/pf_a5_d.v's internal points, and the closed call-site lemma of the trim call:

     a5_trim_site_ok  VERIFY rule 1j-bis: the call at 0x87f44 supplies every premise of trim_contract
                      (lib/A/Prog/trim_c.v) besides afn_pre, out of INV_C alone -- arodata_okP, a0 with its
                      range, trim_pre (p <> 0, sa_str, sa_addr, sa_dst's FRAME arm, the interceptor's range
                      bound) and the event bound. No Section hypothesis.
     a5_c_ok          C (0x87f3c) -> R5 (0x87f48): `addi s9,zero,9`, `ld a0,0xb8(s1)` (slot 0xb8 = buf,
                      pf_pieces.v PF_SL), `jal trim` (listing target pa_sigma SS_trim = BASE + AF_trim by
                      SIGP). The call is stepped by PaNoChain.v cl_callS_wide, whose footprint clause admits
                      trim's one written byte (trim_end_addr buf sl) because it lies in buf, inside the
                      class-5 frame this call owns (awr_byte's in_frames arm); the VIS clause is vacuous,
                      because that byte is below alloc_ceiling while the caller's window is above it. trim's
                      post is apost_base, so the walk stays at the Section's FP state.
     a5_r5_ok         R5 (0x87f48) -> TAIL / HDR / KEY: `mv s7,a0`, inline check 7 (load1 at lp: the token
                      executor's obligation is range_addressable of [lp, lp + 1), which buf's zero shadow
                      gives), `lbu a0,0(s7)` and the two branches on the first byte of the trimmed line:
                      0 -> TAIL at the next line (after `ld s4,0xb0(s1)` reloads cur), '[' -> HDR, else KEY.

   WHERE THE TRIMMED LINE COMES FROM. INV_C holds the stripped line sl = r_strip_comment (pf_line s o) and
   its NUL in buf; trim's post gives a0 = buf + trim_lead sl, the kept prefix firstn (trim_lead sl +
   |r_trim sl|) sl with a NUL after it, and sa_kept for every other byte outside [s1 - STK_trim, s1). Since
   pf_tline s o = r_trim (r_strip_comment (pf_line s o)) = r_trim sl and L_trim_holds (lib/Prog/pfA_facts.v)
   says r_trim sl = firstn |r_trim sl| (skipn (trim_lead sl) sl) with no NUL in it, the bytes at
   lp = buf + trim_lead sl are exactly pf_tline s o and its NUL: INV_R5's sa_str. The slack after that NUL is
   frame bytes, present at the cut (a5_geo) and kept by the call.

   HYPOTHESES. Section e takes TRIM (trim_contract at image A's numbers, at every FP state) and SIGP (the
   call target of a program function, SegObj.v seg_sig_prog). It takes NEITHER SSPX NOR VRO: pf_base after
   the call is rebuilt with pf_a5_k.v's a5_move0, where the stack-protector cells and the read-only window
   are kept bytes (a5_keep_ssp / a5_keep_rod0 inside a5_keep_obj0), per the segment prover's instruction of
   2026-10-30.

   DONORS, all in this clone unless said otherwise. The seeds and the register readers follow segment A7's
   lib/A/Prog/pf_a7_q.v (commit 7831f455a1ce; read-only -- its
   a7_shb_line / a7q_byte_self / a7q_val_mem1 / a7_seed shape and the a7_addr_buf / a7_fframe_buf of its
   pf_a7_d.v are reproduced here under a5tr_ names, over pf_base instead of a7_st, and its a7_trim_call of
   pf_a7_s.v is the shape of a5_trim_call). The token run, the branch lemmas and the kept-memory bookkeeping
   follow the trim walk's trim_l.v / trim_tr.v / trim_s.v / trim_t.v; a5tr_den_off / a5tr_den_atom0 / a5tr_in follow
   segment A2's pf_a2_g.v (pa2_den_off :65, pa2_crt_den_atom0 :63, pa2_in :78), a5tr_bvr its pf_a2.v:70, and a
   register of a list is pf_a5_k.v's a5_rg_get; a5tr_ag32 / a5tr_ag_ew are trim_k.v:364-368. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c trim_c reac_segconf_parse_file_c
  SegInstA pf_pieces pf_a5_d pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== small pure facts ============================== *)
(* buf's shadow cells (8 .. 71) are 0 while buf is in scope (pf_a7_d.v a7_shb_line) *)
Lemma a5tr_shb_line : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0.
Proof.
intros i Hi. unfold pf_shb.
destruct (Z.ltb_spec i 4) as [H|_]; [lia|].
destruct (Z.ltb_spec i 6) as [H|_]; [lia|].
destruct (Z.ltb_spec i 8) as [H|_]; [lia|].
destruct (Z.ltb_spec i 72) as [_|H]; [reflexivity|lia].
Qed.
Lemma a5tr_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma a5tr_m32_16 : forall a, a mod 32 = 0 -> a mod 16 = 0.
Proof.
intros a H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->].
replace (q * 32) with ((2 * q) * 16) by lia. apply Z_mod_mult.
Qed.

(* the environment / denotation readers (pf_a2_g.v pa2_crt_den_atom0 :63, pa2_den_off :65) *)
Lemma a5tr_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma a5tr_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma a5tr_bvr : forall (rr : bvmap 5 word) (r : bv 5) k x, bv_unsigned r = k ->
  getr rr (Z_to_bv 5 k) = x -> getr rr r = x.
Proof. intros rr r k x Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma a5tr_rbv : forall (rr : bvmap 5 word) (r : bv 5) k x, bv_unsigned r = k ->
  getr rr r = x -> getr rr (Z_to_bv 5 k) = x.
Proof. intros rr r k x Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Ltac a5tr_in := cbn [In app]; repeat first [left; reflexivity | right].

(* trim_k.v:364-368 *)
Lemma a5tr_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof.
intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia].
Qed.
Lemma a5tr_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat ->
  ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.

(* the two branch shapes of R5 (trim_s.v tr_br_eq0's form) *)
Lemma a5tr_br_eq_lit : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> (v =? z) = b.
Proof.
intros E n v z b H Hv Hz Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.
Lemma a5tr_br_ne_lit : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> negb (v =? z) = b.
Proof.
intros E n v z b H Hv Hz Hc. rewrite branch_ne_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.

(* a byte of a C string (sa_zs over s ++ [0]) at an index at most its length *)
Lemma a5tr_zs_nth : forall (rd : reader) p s i, sa_zs rd p (s ++ [0]) -> (i <= length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i s 0).
Proof.
intros rd p s i H Hi.
assert (Hlt : (i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
rewrite (H i Hlt). f_equal.
destruct (Nat.lt_ge_cases i (length s)) as [Hl | Hg].
- apply app_nth1. exact Hl.
- assert (i = length s) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  rewrite nth_overflow by lia. reflexivity.
Qed.
Lemma a5tr_hd0_at : forall (rd : reader) p l, sa_str rd p l -> rd p = Some (hd0 l).
Proof.
intros rd p l ((Hzs & _) & _).
pose proof (a5tr_zs_nth rd p l 0%nat Hzs ltac:(lia)) as E. cbn [Z.of_nat] in E. rewrite Z.add_0_r in E.
rewrite E. f_equal. destruct l; reflexivity.
Qed.
(* nth through firstn / skipn, for r_trim's shape *)
Lemma a5tr_nth_firstn : forall (l : list Z) n i, (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
intros l n; revert l; induction n as [|n IH]; intros l i Hi; [lia|].
destruct l as [|x l]; cbn [firstn]; [reflexivity|].
destruct i as [|i]; cbn [nth]; [reflexivity | apply IH; lia].
Qed.
Lemma a5tr_nth_skipn : forall (l : list Z) n i, nth i (skipn n l) 0 = nth (n + i) l 0.
Proof.
intros l n. revert l. induction n as [|n IH]; intros [|x l] i; cbn [skipn Nat.add nth]; try reflexivity.
- destruct i; reflexivity.
- rewrite IH. reflexivity.
Qed.

(* ============================== the symbolic states ============================== *)
(* C (0x87f3c): the one spill slot the run reads, s1 + 0xb8 = buf (PF_SL). Atom 32 = F. *)
Definition a5c_slot_r : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xb8 0xc0 0 0 [YP09.mkChunk 0xb8 (CVal 8 (SOff 32 PF_O_BUF))].
Definition a5c_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
            (22%nat, mkAF SB SB 0); (32%nat, PTR 5) ] [] [].
Definition a5c_ss : sstate := mkSS A5_C sr_atoms [a5c_slot_r] None a5c_facts.
(* R5 (0x87f48): the byte at lp (region on atom 10, value atom 33) and the slot s1 + 0xb0 = cur (atom 32),
   both read-only: A5 writes nothing between R5 and its exits. *)
Definition a5r_byte_r : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition a5r_slot_r : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xb0 0xb8 0 0 [YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0))].
Definition a5r_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
            (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (22%nat, mkAF SB SB 0); (33%nat, mkAF 0 255 0) ] [] [].
Definition a5r_ss : sstate := mkSS A5_R5 sr_atoms [a5r_byte_r; a5r_slot_r] None a5r_facts.
(* the shadow base of A5's inline checks is s6 (pf_fi: getr rX 22 = w64 SHADOW_OFF) *)
Definition a5_Bx : sv := SOff 22 0.
(* the registers the two runs leave as their own atoms *)
Definition a5c_keep : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27].
Definition a5r_keep : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27].
Definition a5r_keep_t : list Z := [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 26; 27].
Lemma a5tr_keep_sub : forall kk, In kk a5r_keep_t -> In kk a5r_keep.
Proof. intros kk H. unfold a5r_keep, a5r_keep_t in *. cbn [In] in *. tauto. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a word read through the state's reader is a 64-bit value *)
Lemma a5tr_rdword_rng : forall (H : word -> bool) mem a v, rdword (aview SEGS H mem) a = Some v ->
  0 <= v < 2 ^ 64.
Proof.
intros H mem a v E. unfold rdword in E.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection E as <-.
pose proof (sa_aview_rng _ _ _ _ _ E0). pose proof (sa_aview_rng _ _ _ _ _ E1).
pose proof (sa_aview_rng _ _ _ _ _ E2). pose proof (sa_aview_rng _ _ _ _ _ E3).
pose proof (sa_aview_rng _ _ _ _ _ E4). pose proof (sa_aview_rng _ _ _ _ _ E5).
pose proof (sa_aview_rng _ _ _ _ _ E6). pose proof (sa_aview_rng _ _ _ _ _ E7).
lia.
Qed.
(* the reader depends on the address only through its 64-bit truncation, so a fact given on [0, 2 ^ 64)
   holds everywhere *)
Lemma a5tr_view_wrap : forall (H : word -> bool) mem a b, Z_to_bv 64 a = Z_to_bv 64 b ->
  aview SEGS H mem a = aview SEGS H mem b.
Proof. intros H mem a b E. unfold aview, YP09.mbyte. rewrite E. reflexivity. Qed.
Lemma a5tr_vis_all : forall (W W' : world SEGS) mem mem',
  (forall a, 0 <= a < 2 ^ 64 -> rdW W mem a <> None -> rdW W' mem' a <> None) ->
  forall a, rdW W mem a <> None -> rdW W' mem' a <> None.
Proof.
intros W W' mem mem' Hv a Ha.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hb.
assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zmod_mod. reflexivity. }
rewrite (a5tr_view_wrap (w_H W') mem' a (a mod 2 ^ 64) E).
apply Hv; [lia|]. rewrite <- (a5tr_view_wrap (w_H W) mem a (a mod 2 ^ 64) E). exact Ha.
Qed.
(* one byte of the reader as a one-byte chunk (pf_a7_q.v a7q_val_mem1) *)
Lemma a5tr_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma a5tr_val_mem1 : forall (H : word -> bool) (mem : word -> option byte) a z,
  aview SEGS H mem a = Some z -> 0 <= z < 256 -> val_mem SEGS (mrestrict H mem) a 1 z.
Proof.
intros H mem a z Hv Hz k Hk. assert (k = 0%nat) as -> by lia.
destruct (aview_byte SEGS H mem a z Hv) as (b & Hb & Hvb & _).
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Hvb.
symmetry. apply a5tr_byte_self.
Qed.

(* the environments *)
Definition a5c_E (rX : bvmap 5 word) (v : pfv) (pos : Z) : env := Eimg (Ereg rX [w64 (pf_F v pos)]).
Definition a5r_E (rX : bvmap 5 word) (cp hd : Z) : env := Eimg (Ereg rX [w64 cp; w64 hd]).

Lemma a5c_E_img : forall rX v pos, img_env VAL A_LIM (a5c_E rX v pos).
Proof. intros rX v pos. unfold a5c_E. apply Eimg_env. Qed.
Lemma a5r_E_img : forall rX cp hd, img_env VAL A_LIM (a5r_E rX cp hd).
Proof. intros rX cp hd. unfold a5r_E. apply Eimg_env. Qed.
Lemma a5c_E_agree : forall rX v pos, env_agree 32 (Ereg rX [w64 (pf_F v pos)]) (a5c_E rX v pos).
Proof.
intros rX v pos. split; [|reflexivity]. intros n Hn. unfold a5c_E. apply Eimg_low. unfold A_TEXT. lia.
Qed.
Lemma a5r_E_agree : forall rX cp hd, env_agree 32 (Ereg rX [w64 cp; w64 hd]) (a5r_E rX cp hd).
Proof.
intros rX cp hd. split; [|reflexivity]. intros n Hn. unfold a5r_E. apply Eimg_low. unfold A_TEXT. lia.
Qed.
Lemma a5c_ew_reg : forall rX v pos k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (a5c_E rX v pos) k = getr rX r.
Proof. intros rX v pos k r Hk. unfold a5c_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.
Lemma a5r_ew_reg : forall rX cp hd k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (a5r_E rX cp hd) k = getr rX r.
Proof. intros rX cp hd k r Hk. unfold a5r_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.
Lemma a5c_ew_F : forall rX v pos, ew (a5c_E rX v pos) 32 = Z_to_bv 64 (pf_F v pos).
Proof.
intros rX v pos. unfold a5c_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 0).
Qed.
Lemma a5r_ew_cp : forall rX cp hd, ew (a5r_E rX cp hd) 32 = Z_to_bv 64 cp.
Proof.
intros rX cp hd. unfold a5r_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 0).
Qed.
Lemma a5r_ew_hd : forall rX cp hd, ew (a5r_E rX cp hd) 33 = Z_to_bv 64 hd.
Proof.
intros rX cp hd. unfold a5r_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra rX [w64 cp; w64 hd] 1).
Qed.
(* the registers a run left as their own atoms keep the seed's values (pf_a7_q.v a7_regs_kept) *)
Lemma a5tr_regs_kept : forall rX (extra : list word) (E : env) ss (H : word -> bool) ms (l : list Z),
  st_ok SEGS E ss (restrict H ms) -> env_agree 32 (Ereg rX extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    (map (Z_to_bv 5) l) = true ->
  forall k, In k l -> getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k).
Proof.
intros rX extra E ss H ms l HS HA Hl k Hk.
exact (regs_kept_of_st_ok SEGS E ss (restrict H ms) rX extra (map (Z_to_bv 5) l) HS HA Hl
  (Z_to_bv 5 k) (in_map _ _ _ Hk)).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* trim's contract at image A's numbers, at every FP state (lib/A/Prog/trim_c.v) *)
Hypothesis TRIM : forall fx0 : YK11.FPState,
  trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
(* the call target of every program function (SegObj.v) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Ltac a5tr_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* after a run that writes nothing (trim_l.v tl_after) *)
Ltac a5tr_after E0 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    lazymatch type of HAE with env_agree ?k _ _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    assert (KPn : forall a, aview SEGS (w_H _) _ a <> None -> aview SEGS (w_H _) (ms_mem msn) a <> None)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          exact (aview_keeps_vis SEGS (w_H _) _ (ms_mem msn) a HG (KP a Ha)));
    clear HFr HG HAE KM KP; rename HAEn into HAE; rename KMn into KM; rename KPn into KP;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
    end
  end.

(* ============================== buf, and what a callee asks of it ============================== *)
Lemma a5tr_buf_rng : forall v pos, a5_G v pos ->
  4096 < a5_buf v pos /\ a5_buf v pos + 512 <= alloc_ceiling /\
  pf_F v pos <= a5_buf v pos /\ a5_buf v pos + 512 <= pf_F v pos + 2048 /\ pf_F v pos mod 8 = 0.
Proof.
intros v pos (_ & _ & _ & _ & _ & G6 & G7 & G8 & _).
pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (pf_F v pos) 32 ltac:(lia)) as M.
unfold a5_buf, PF_O_BUF.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
apply Z.mod_divide in G8; [|lia]. destruct G8 as [q Hq]. rewrite Hq.
replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.
(* buf's shadow cell for an address of buf (pf_a7_d.v a7_sh_at) *)
Lemma a5tr_sh_at : forall v pos lyc Sc Wc rX memc mdc x,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> a5_G v pos ->
  a5_buf v pos <= x < a5_buf v pos + 512 ->
  rdW Wc memc (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
intros v pos lyc Sc Wc rX memc mdc x HB G Hx.
destruct (a5tr_buf_rng v pos G) as (H1 & H2 & HF1 & HF2 & HF8).
destruct HB as (_ & _ & _ & _ & HFSH).
unfold a5_buf, PF_O_BUF in Hx.
replace x with (pf_F v pos + (x - pf_F v pos)) by lia.
rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos).
rewrite (HFSH ((x - pf_F v pos) / 8)).
- f_equal. apply a5tr_shb_line.
  split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
- split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma a5tr_sh_some : forall v pos lyc Sc Wc rX memc mdc s,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  pf_SH v pos <= s < pf_SH v pos + 144 -> rdW Wc memc s <> None.
Proof.
intros v pos lyc Sc Wc rX memc mdc s HB Hs.
destruct HB as (_ & _ & _ & _ & HFSH).
replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
rewrite (HFSH (s - pf_SH v pos) ltac:(lia)). discriminate.
Qed.
(* a range of buf is addressable with its shadow mapped (pf_a7_d.v a7_addr_buf) *)
Lemma a5tr_addr_buf : forall v pos lyc Sc Wc rX memc mdc q n,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> a5_G v pos ->
  a5_buf v pos <= q -> 0 <= n -> q + n <= a5_buf v pos + 512 ->
  sa_addr (rdW Wc memc) q n.
Proof.
intros v pos lyc Sc Wc rX memc mdc q n HB G Hq Hn Hqn.
destruct (a5tr_buf_rng v pos G) as (H1 & H2 & HF1 & HF2 & HF8).
pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & G9 & _).
pose proof alloc_ceiling_lt as HC.
unfold a5_buf, PF_O_BUF in H1, H2, HF1, HF2, Hq, Hqn.
split; [lia|]. split; [lia|].
split.
{ apply amem_range_high; [lia | | lia].
  destruct G9 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
  [left; lia | right; lia]. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  apply (a5tr_sh_at v pos lyc Sc Wc rX memc mdc x HB G). unfold a5_buf, PF_O_BUF. lia.
- intros Hn0 s Hs.
  assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8).
  { unfold shadow_addr. replace q with (pf_F v pos + (q - pf_F v pos)) at 1 by lia.
    change (SHADOW_OFF + (pf_F v pos + (q - pf_F v pos)) / 8)
      with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q - pf_F v pos))).
    rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q - pf_F v pos) HF8). reflexivity. }
  assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8).
  { unfold shadow_addr. replace (q + n - 1) with (pf_F v pos + (q + n - 1 - pf_F v pos)) at 1 by lia.
    change (SHADOW_OFF + (pf_F v pos + (q + n - 1 - pf_F v pos)) / 8)
      with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q + n - 1 - pf_F v pos))).
    rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q + n - 1 - pf_F v pos) HF8). reflexivity. }
  assert (B1 : 8 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 72) by (apply Z.div_lt_upper_bound; lia).
  rewrite E1, E2 in Hs.
  apply (a5tr_sh_some v pos lyc Sc Wc rX memc mdc s HB).
  pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
  lia.
Qed.
Lemma a5tr_fframe_buf : forall v pos lyc Sc q n, In (5, pos) (frames Sc) -> lyc = p_ly v ->
  a5_buf v pos <= q -> 0 <= n -> q + n <= a5_buf v pos + 512 -> sa_fframe lyc Sc q n.
Proof.
intros v pos lyc Sc q n Hin Hly Hq Hn Hqn.
exists 5, pos. split; [exact Hin|]. split; [lia|].
unfold a5_buf, PF_O_BUF, pf_F in Hq, Hqn. rewrite <- Hly in Hq, Hqn.
change (fs_frame_bytes 5) with 2048. lia.
Qed.
Lemma a5tr_room_ev : forall v pos lyc Sc Wc rX memc mdc sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> sa_room Sc /\ st_nev Sc <= EV_MAX.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & (HJ & _) & _).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HROOM & HEV).
pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev & _).
unfold sa_room_n in HROOM. unfold EV_reac_segconf_parse_file in HEV.
split; [|lia]. unfold sa_room. rewrite Hfr, length_app. cbn [length]. lia.
Qed.
(* the stripped line of INV_C: no NUL, no longer than the line *)
Lemma a5tr_sl_facts : forall s o, ~ In 0 s ->
  ~ In 0 (r_strip_comment (pf_line s o)) /\
  (length (r_strip_comment (pf_line s o)) <= length (pf_line s o))%nat.
Proof.
intros s o HNZ.
destruct (L_line_bytes_holds s o HNZ) as (_ & HNZl & _).
split; [|apply r_strip_comment_len_le].
destruct (L_strip_holds (pf_line s o) HNZl) as (k & Hk & Ek & _ & _).
rewrite Ek. intros Hin. apply HNZl.
rewrite <- (firstn_skipn k (pf_line s o)). apply in_or_app. left. exact Hin.
Qed.

(* a reader fact kept across a step that writes nothing: the reader depends on the address only through its
   64-bit truncation, so an agreement on [0, 2 ^ 64) is an agreement everywhere *)
Lemma a5tr_keep_all : forall (W : world SEGS) mem mem',
  (forall a, 0 <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a) -> forall a, rdW W mem' a = rdW W mem a.
Proof.
intros W mem mem' HK a.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hb.
assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zmod_mod. reflexivity. }
rewrite (a5tr_view_wrap (w_H W) mem' a _ E), (a5tr_view_wrap (w_H W) mem a _ E). apply HK. lia.
Qed.
Lemma a5tr_addr_keep : forall (rd rd' : reader) q n, (forall a, rd' a = rd a) ->
  sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n HK (A0 & A1 & A2 & A3 & A4).
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [rewrite HK; exact Hs | exact Hok].
- intros Hn s Hs. rewrite HK. exact (A4 Hn s Hs).
Qed.
Lemma a5tr_str_keep : forall (rd rd' : reader) p l, (forall a, rd' a = rd a) ->
  sa_str rd p l -> sa_str rd' p l.
Proof.
intros rd rd' p l HK ((H1 & H2) & H3). split; [split|].
- intros i Hi. rewrite HK. exact (H1 i Hi).
- exact H2.
- intros x Hx. rewrite HK. exact (H3 x Hx).
Qed.
Lemma a5tr_rod_keep : forall (rd rd' : reader), (forall a, rd' a = rd a) ->
  arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof. intros rd rd' HK H a Hro Ho He. rewrite HK. exact (H a Hro Ho He). Qed.

(* ============================== VERIFY rule 1j-bis: the trim call at 0x87f44 ============================== *)
(* everything trim_contract asks besides afn_pre, which the call rule builds from the caller's journal *)
Definition a5_trim_call (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (regs : bvmap 5 word) (p : Z) (s : list Z) : Prop :=
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 p /\ 0 <= p < 2 ^ 64 /\
  trim_pre SEGS B lyc Sc Wc memc regs p s /\
  st_nev Sc + EV_trim <= EV_MAX.

Lemma a5_trim_site_ok : forall n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d (regsc : bvmap 5 word) memc',
  INV_C B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  (forall a, rdW Wc memc' a = rdW Wc memc a) ->
  getr regsc 10 = w64 (a5_buf v pos) ->
  a5_trim_call lyc Sc Wc memc' regsc (a5_buf v pos) (r_strip_comment (pf_line (p_s v) o)).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d regsc memc' HI HK R10.
pose proof HI as (HB & HLN & HSL & HLT & HZS & HRG).
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & _).
destruct (a5tr_buf_rng v pos G) as (Hb0 & Hb1 & HF1 & HF2 & HF8).
destruct (a5tr_room_ev v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & HEV).
destruct (a5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HNZ & _ & _ & _ & _ & _).
pose proof HB as (_ & _ & HOBJ & _).
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
pose proof alloc_ceiling_lt as HC.
destruct (a5tr_sl_facts (p_s v) o HNZ) as (HNZs & HLs).
unfold a5_len in HLT.
assert (HLs512 : (length (r_strip_comment (pf_line (p_s v) o)) < 512)%nat) by lia.
assert (HA : sa_addr (rdW Wc memc) (a5_buf v pos)
               (Z.of_nat (length (r_strip_comment (pf_line (p_s v) o))) + 1))
  by (apply (a5tr_addr_buf v pos lyc Sc Wc rX memc mdc); [exact HB | exact G | lia | lia | lia]).
pose proof HA as (_ & _ & _ & HRA & _).
assert (HSTR : sa_str (rdW Wc memc) (a5_buf v pos) (r_strip_comment (pf_line (p_s v) o))).
{ split; [split; [exact HZS | exact HNZs]|].
  intros x Hx.
  pose proof (Z.mod_pos_bound (a5_buf v pos + Z.of_nat (length (r_strip_comment (pf_line (p_s v) o)))) 8
                ltac:(lia)) as Hm.
  apply (aview_some_of_apresent SEGS). apply HFP. unfold a5_buf, PF_O_BUF in *. lia. }
pose proof (a5tr_addr_keep _ _ _ _ HK HA) as HA'.
pose proof HA' as (_ & _ & _ & HRA' & _).
unfold a5_trim_call.
split; [exact (a5tr_rod_keep _ _ HK HROD)|]. split; [exact R10|]. split; [lia|].
split; [|unfold EV_trim; lia].
unfold trim_pre.
split; [lia|]. split; [exact (a5tr_str_keep _ _ _ _ HK HSTR)|]. split; [exact HA'|].
split; [|lia].
left. split; [|exact HRA'].
apply (a5tr_fframe_buf v pos lyc Sc); [exact Hin | exact Hly | lia | lia | lia].
Qed.

(* ============================== the seeds ============================== *)
Lemma a5c_seed : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  st_ok_pi SEGS VAL (a5c_E rX v pos) a5c_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + A5_C)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc HB.
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _ & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (_ & _ & _ & HSL & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v))
  by (eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v))
  by (eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF)
  by (eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]).
assert (Hb8 : rdword (rdW Wc memc) (pf_s1 v + 0xb8) = Some (pf_F v pos + PF_O_BUF))
  by (exact (proj1 (Forall_forall _ _) HSL (0xb8, pf_F v pos + PF_O_BUF) ltac:(unfold PF_SL; a5tr_in))).
assert (U2 : bv_unsigned (ew (a5c_E rX v pos) 2) = pf_s1 v).
{ rewrite (a5c_ew_reg rX v pos 2 (Z_to_bv 5 2) eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (U9 : bv_unsigned (ew (a5c_E rX v pos) 9) = pf_s1 v).
{ rewrite (a5c_ew_reg rX v pos 9 (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (U22 : bv_unsigned (ew (a5c_E rX v pos) 22) = SB).
{ rewrite (a5c_ew_reg rX v pos 22 (Z_to_bv 5 22) eq_refl), R22. unfold w64, SB, SHADOW_OFF.
  apply unsigned_lit_small. lia. }
assert (U32 : bv_unsigned (ew (a5c_E rX v pos) 32) = pf_F v pos)
  by (rewrite a5c_ew_F; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold a5c_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold a5c_slot_r. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ (pf_s1 v) 0xb8 8%N (SOff 32 PF_O_BUF) (pf_F v pos + PF_O_BUF)).
  + rewrite (a5tr_den_off _ 32 (pf_F v pos) PF_O_BUF (a5c_ew_F rX v pos) ltac:(lia)). reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold PF_O_BUF. lia.
  + lia.
  + exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hb8).
- cbn. tauto.
- split; [|split; exact I].
  cbn [a5c_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U22, U32.
  try change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  rewrite G5, G8. unfold SB. repeat split; lia.
Qed.

Lemma a5r_seed : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc lp cp hd,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> a5_G v pos ->
  getr rX (Z_to_bv 5 10) = w64 lp -> a5_buf v pos <= lp < a5_buf v pos + 512 ->
  rdW Wc memc lp = Some hd -> 0 <= hd <= 255 ->
  rdword (rdW Wc memc) (pf_s1 v + 0xb0) = Some cp -> 0 <= cp < 2 ^ 64 ->
  st_ok_pi SEGS VAL (a5r_E rX cp hd) a5r_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + A5_R5)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc lp cp hd HB G R10 Hlp Hhdr Hhd Hb0 Hcp.
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
destruct (a5tr_buf_rng v pos G) as (Hq0 & Hq1 & HF1 & HF2 & HF8).
unfold a5_buf, PF_O_BUF in Hq0, Hq1, HF1, HF2, Hlp.
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v))
  by (eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v))
  by (eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF)
  by (eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]).
assert (U2 : bv_unsigned (ew (a5r_E rX cp hd) 2) = pf_s1 v).
{ rewrite (a5r_ew_reg rX cp hd 2 (Z_to_bv 5 2) eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (U9 : bv_unsigned (ew (a5r_E rX cp hd) 9) = pf_s1 v).
{ rewrite (a5r_ew_reg rX cp hd 9 (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (U10 : bv_unsigned (ew (a5r_E rX cp hd) 10) = lp).
{ rewrite (a5r_ew_reg rX cp hd 10 (Z_to_bv 5 10) eq_refl), R10. unfold w64. apply unsigned_lit_small. lia. }
assert (U22 : bv_unsigned (ew (a5r_E rX cp hd) 22) = SB).
{ rewrite (a5r_ew_reg rX cp hd 22 (Z_to_bv 5 22) eq_refl), R22. unfold w64, SB, SHADOW_OFF.
  apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew (a5r_E rX cp hd) 33) = hd)
  by (rewrite a5r_ew_hd; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold a5r_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok, a5r_byte_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ lp 0 1%N (SOff 33 0) hd).
    * rewrite a5tr_den_atom0, a5r_ew_hd. reflexivity.
    * change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    * lia.
    * rewrite Z.add_0_r. apply a5tr_val_mem1; [exact Hhdr | lia].
  + unfold region_ok, a5r_slot_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ (pf_s1 v) 0xb0 8%N (SOff 32 0) cp).
    * rewrite a5tr_den_atom0, a5r_ew_cp. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hb0).
- unfold a5r_byte_r, a5r_slot_r. cbn [YP09.pairwise_disjoint YP09.all_disjoint].
  unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite U9, U10. repeat split; lia.
- split; [|split; exact I].
  cbn [a5r_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U10, U22, U33.
  try change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  rewrite G5. unfold SB. repeat split; lia.
Qed.

(* ============================== pf_base and pf_st across a run that writes nothing ============== *)
Lemma a5tr_base_keep : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc sc rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  pf_rg rX' (a5_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' HB HJ HK HV HRG.
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (_ & _ & _ & G & _ & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & _ & _ & HFSH).
apply (a5_move0 B v pos lyc Sc Wc rX memc mdc sc Sc Wc rX' memc' mdc' sc HB HJ).
- exists (st_fs Sc). destruct Sc; reflexivity.
- apply Permutation_refl.
- intros a Ha _. exact (HK a Ha).
- exact HV.
- exact HRG.
- intros i Hi. rewrite HK by (unfold kHighShadowEnd in G12; lia). exact (HFSH i Hi).
Qed.

(* ============================== C (0x87f3c) -> R5: the trim call ============================== *)
Lemma a5_c_ok : forall n, H_R5 B n -> H_C B n.
Proof.
intros n HR5 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLN & HSL & HLT & HZS & HRG).
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & HSHP).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (HCX & HJI & HOBJ & HSLL & HFSH).
pose proof HJI as (HJ & Hly0 & HSfs & HPerm0 & HSAV & HFL & HFRM & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (STKT & _ & _ & SPF & _).
pose proof alloc_ceiling_lt as HC.
destruct (a5tr_buf_rng v pos G) as (Hb0 & Hb1 & HF1 & HF2 & HF8).
destruct (a5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HNZ & HLSZ & _ & _ & _ & HCHEAP).
destruct (a5tr_sl_facts (p_s v) o HNZ) as (HNZs & HLs).
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
unfold a5_len in HLT.
set (sl := r_strip_comment (pf_line (p_s v) o)) in *.
set (k := seg_spec.trim_lead sl) in *.
set (m := length (SegModel.r_trim sl)) in *.
destruct (L_trim_holds sl HNZs) as (HTL1 & HTL2 & HTL3).
assert (HKM : (k + m <= length sl)%nat) by exact HTL1.
assert (HTLN : pf_tline (p_s v) o = SegModel.r_trim sl) by reflexivity.
(* the seed and the run to the call *)
pose proof (a5c_seed v pos lyc Sc Wc rX memc mdc HB) as HS.
pose proof (a5c_E_img rX v pos) as HEI.
pose proof (a5c_E_agree rX v pos) as HA0.
assert (E32 : ew (a5c_E rX v pos) 32 = Z_to_bv 64 (pf_F v pos)) by apply a5c_ew_F.
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew (a5c_E rX v pos) kk = getr rX r)
  by (intros kk r Hk0; apply a5c_ew_reg; exact Hk0).
assert (SHOK : sh_ok SEGS a5_Bx [] (a5c_E rX v pos) (mrestrict (w_H Wc) memc)) by constructor.
revert HS HEI HA0 E32 EE SHOK. generalize (a5c_E rX v pos) as E0. intros E0 HS HEI HA0 E32 EE SHOK.
unfold cfg_at. change (w64 (BASE + A5_C)) with (Z_to_bv 64 (BASE + A5_C)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ a5tr_awr. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (let Hq := fresh "Hq" in destruct Hin' as [Hq | Hin'];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
  destruct Hin'. }
assert (KP : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
lazymatch type of HS with
| st_ok _ ?En _ _ => assert (HAE : env_agree 33 E0 En) by (env_agree_chain (env_agree_refl 33 E0))
end.
clear HFr HG HF.
(* the registers at the call *)
assert (QK : forall kk, In kk a5c_keep -> getr (ms_regs ms) (Z_to_bv 5 kk) = getr rX (Z_to_bv 5 kk)).
{ eapply (a5tr_regs_kept rX [w64 (pf_F v pos)] _ _ (w_H Wc) ms a5c_keep HS);
    [exact (a5tr_ag32 rX _ E0 _ 33 ltac:(lia) HA0 HAE) | vm_compute; reflexivity]. }
prreg HS (1%bv : bv 5) Q1.
prreg HS (10%bv : bv 5) Q10.
prreg HS (25%bv : bv 5) Q25.
rewrite E32 in Q10.
assert (Q1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 12820))
  by (rewrite Q1; first [reflexivity | apply (codeptr_val _ 12820 HEI)]).
assert (Q10' : getr (ms_regs ms) 10 = w64 (a5_buf v pos)).
{ rewrite Q10. unfold w64, a5_buf, PF_O_BUF.
  first [reflexivity | (rewrite unsigned_lit_small by lia; reflexivity)]. }
assert (Q2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ apply (a5tr_bvr _ _ 2); [reflexivity|]. rewrite (QK 2 ltac:(unfold a5c_keep; a5tr_in)).
  eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]. }
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ apply (a5tr_bvr _ _ 3); [reflexivity|]. rewrite (QK 3 ltac:(unfold a5c_keep; a5tr_in)).
  eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]. }
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ apply (a5tr_bvr _ _ 4); [reflexivity|]. rewrite (QK 4 ltac:(unfold a5c_keep; a5tr_in)).
  eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]. }
assert (Q8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v)).
{ apply (a5tr_bvr _ _ 8); [reflexivity|]. rewrite (QK 8 ltac:(unfold a5c_keep; a5tr_in)).
  eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]. }
assert (Rsp : spZ (ms_regs ms) = pf_s1 v)
  by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (Rs0 : s0Z (ms_regs ms) = pf_sp0 v)
  by (unfold s0Z; rewrite Q8; unfold w64; apply unsigned_lit_small; lia).
pmkst HS.
(* the chain the callee's afn_pre asks for, at the call's reader *)
destruct (a5_chain B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (ch1 & HCH).
pose proof HJ as (_ & HlyOK & _).
pose proof HlyOK as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HCH' : achain lyc (rdW Wc (ms_mem ms)) (pf_s1 v) (pf_sp0 v) ch1).
{ apply (achain_kept lyc (rdW Wc memc) (rdW Wc (ms_mem ms)) (pf_s1 v) (pf_sp0 v) ch1 0 HCH);
    [lia | lia | intros a Ha; apply KM; lia]. }
(* the site: trim's premises *)
pose proof (a5_trim_site_ok n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d (ms_regs ms) (ms_mem ms) HI
  (a5tr_keep_all Wc memc (ms_mem ms) KM) Q10') as (SROD & SR10 & SR64 & STP & SEVT).
(* the call at 0x87f44: cl_callS_wide, the footprint byte inside the frame *)
rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; a5tr_in)).
replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc _ 0
    STK_trim [(trim_end_addr (a5_buf v pos) sl, trim_end_addr (a5_buf v pos) sl + 1)] EV_trim
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + 12820)) ch1
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (a5_buf v pos + Z.of_nat k) /\
       sa_bytes (rdW W' mem') (a5_buf v pos)
         (seg_spec.zb (firstn (k + m) sl) ++ [seg_spec.ZERO]) /\
       sa_kept SEGS Wc (ms_mem ms) W' mem' (ms_regs ms) STK_trim
         (fun a => a = trim_end_addr (a5_buf v pos) sl) /\
       sa_noalloc B lyc Sc ly' S') HJ).
  - rewrite Rsp. lia.
  - apply a5tr_m16; [apply a5tr_m32_16; exact G5 | exact G3].
  - lia.
  - unfold STK_trim, YG0d.ESTACK. lia.
  - rewrite STKT, SPF. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1'.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof pa_B_ok as (HB0 & HB1 & _). rewrite unsigned_lit_small by lia. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia. rewrite Rs0. exact HCH'.
  - intros HPRE1. eapply SRr_mono.
    { apply (TRIM fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ ch1 (a5_buf v pos) sl HPRE1 SROD SR10 SR64 STP
        SEVT). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. split; [rewrite Q1'; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - (* the footprint byte is one the caller may write: it lies in the class-5 frame it owns *)
    intros a (r0 & Hr0 & Hra). cbn [In] in Hr0. destruct Hr0 as [<- | []]. cbn [fst snd] in Hra.
    unfold trim_end_addr in Hra.
    right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 5) with 2048.
    replace (frame_addr lyc 5 pos) with (pf_F v pos) by (unfold pf_F; rewrite Hly; reflexivity).
    unfold a5_buf, PF_O_BUF in Hra. lia.
  - (* VIS: vacuous, the byte is below alloc_ceiling and the caller's window is above it *)
    intros ly2 S2 W2 regs2 mem2 md2 _ a (r0 & Hr0 & Hra) Hw _.
    cbn [In] in Hr0. destruct Hr0 as [<- | []]. cbn [fst snd] in Hra. unfold trim_end_addr in Hra.
    exfalso. rewrite SPF in Hw. unfold a5_buf, PF_O_BUF in Hra. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & Ha0 & HBYT & HKEPT & HNA).
destruct HNA as (HPERM2 & Hly2 & (f2 & HS2e)).
rewrite Hly2 in *.
(* what the call kept *)
assert (KOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - STK_trim <= a < pf_s1 v) ->
  a <> trim_end_addr (a5_buf v pos) sl -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hw Hne. rewrite (HKEPT a Ha ltac:(rewrite Rsp; exact Hw) ltac:(cbn; exact Hne)).
  apply KM. exact Ha. }
assert (HTE : trim_end_addr (a5_buf v pos) sl = a5_buf v pos + Z.of_nat (k + m)) by reflexivity.
assert (HZ0 : bv_unsigned seg_spec.ZERO = 0) by (vm_compute; reflexivity).
assert (HLEN : length (seg_spec.zb (firstn (k + m) sl) ++ [seg_spec.ZERO]) = S (k + m))
  by (unfold seg_spec.zb; rewrite length_app, length_map, length_firstn; cbn [length]; lia).
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos false false a -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hn. apply KOUT; [exact Ha| |].
  - intros Hq. apply Hn. unfold a5_Wrx. left. rewrite SPF. lia.
  - intros Hq. apply Hn. unfold a5_Wrx. right; right; left. rewrite Hq, HTE. lia. }
assert (KBIG : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true true a -> rdW W2 mem2 a = rdW Wc memc a)
  by (intros a Ha Hn; apply KALL; [exact Ha | intros Hq; exact (Hn (a5_Wrx_mono v pos false false a Hq))]).
assert (VBIG : forall a, rdW Wc memc a <> None -> rdW W2 mem2 a <> None).
{ apply a5tr_vis_all. intros a Ha Hv.
  destruct (Z_lt_le_dec a (pf_s1 v - STK_trim)) as [Hlo | Hlo];
  [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
  - destruct (Z.eq_dec a (trim_end_addr (a5_buf v pos) sl)) as [-> | Hne].
    + rewrite HTE in *.
      rewrite (HBYT (k + m)%nat ltac:(rewrite HLEN; lia)).
      discriminate.
    + rewrite (KOUT a Ha ltac:(lia) Hne). exact Hv.
  - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite SPF. lia.
  - destruct (Z.eq_dec a (trim_end_addr (a5_buf v pos) sl)) as [-> | Hne].
    + rewrite HTE in *.
      rewrite (HBYT (k + m)%nat ltac:(rewrite HLEN; lia)).
      discriminate.
    + rewrite (KOUT a Ha ltac:(lia) Hne). exact Hv. }
(* the journal's event count *)
replace (0 + EV_trim) with 0 in HJ2 by (unfold EV_trim; lia).
(* pf_base at the return *)
assert (HRG2 : pf_rg regs2 (a5_FI B v)).
{ apply (a5_rg_pres (ms_regs ms) regs2 _ HP2 (a5_FI_cs B v)).
  unfold pf_rg, a5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    lazymatch goal with |- getr _ (Z_to_bv 5 ?rr) = _ =>
      rewrite (QK rr ltac:(unfold a5c_keep; a5tr_in)); eapply a5_rg_get;
      [exact HFI | unfold a5_FI; a5tr_in] end. }
assert (HFSH2 : pf_fsh (rdW W2 mem2) (pf_SH v pos) PF_SC_LINE).
{ apply (a5_keep_fsh v pos (rdW Wc memc) (rdW W2 mem2) false PF_SC_LINE G); [|exact HFSH].
  intros a Ha Hn. apply KALL; [exact Ha | exact Hn]. }
assert (HB2 : pf_base B v pos lyc S2 W2 regs2 mem2 md2 PF_SC_LINE).
{ apply (a5_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE S2 W2 regs2 mem2 md2 PF_SC_LINE HB HJ2);
    [exists f2; exact HS2e | exact HPERM2 | exact KBIG | exact VBIG | exact HRG2 | exact HFSH2]. }
(* the trimmed line at lp = buf + trim_lead sl *)
set (lp := a5_buf v pos + Z.of_nat k) in *.
assert (HRNG : forall i, (i <= length sl)%nat -> 0 <= nth i sl 0 < 256).
{ intros i Hi. exact (sa_aview_rng _ _ _ _ _ (a5tr_zs_nth _ _ sl i HZS Hi)). }
assert (HBY : forall i, (i <= m)%nat ->
  rdW W2 mem2 (lp + Z.of_nat i) = Some (nth i (SegModel.r_trim sl) 0)).
{ intros i Hi.
  replace (lp + Z.of_nat i) with (a5_buf v pos + Z.of_nat (k + i)) by (unfold lp; lia).
  rewrite (HBYT (k + i)%nat ltac:(rewrite HLEN; lia)). f_equal.
  unfold seg_spec.zb, ZB0.
  destruct (Nat.lt_ge_cases i m) as [Hlt | Hge].
  - rewrite app_nth1 by (rewrite length_map, length_firstn; lia).
    rewrite (map_nth (Z_to_bv 8) (firstn (k + m) sl) 0 (k + i)).
    rewrite a5tr_nth_firstn by lia.
    rewrite HTL2, a5tr_nth_firstn by lia. rewrite a5tr_nth_skipn.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 8) with 256. apply HRNG. lia.
  - assert (i = m) as -> by lia.
    rewrite app_nth2 by (rewrite length_map, length_firstn; lia).
    rewrite length_map, length_firstn.
    replace (k + m - Init.Nat.min (k + m) (length sl))%nat with 0%nat by lia.
    cbn [nth]. rewrite HZ0. rewrite nth_overflow by lia. reflexivity. }
assert (HSTR2 : sa_str (rdW W2 mem2) lp (pf_tline (p_s v) o)).
{ rewrite HTLN. split; [split|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (HBY i ltac:(lia)). f_equal.
    destruct (Nat.lt_ge_cases i m) as [Hlt | Hge].
    + rewrite app_nth1 by lia. reflexivity.
    + assert (i = m) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      rewrite nth_overflow by lia. reflexivity.
  - exact HTL3.
  - intros x Hx.
    pose proof (Z.mod_pos_bound (lp + Z.of_nat m) 8 ltac:(lia)) as Hmd.
    destruct (Z_lt_le_dec x (a5_buf v pos + 512)) as [Hin512 | Hout].
    + destruct (Z.eq_dec x (trim_end_addr (a5_buf v pos) sl)) as [-> | Hne].
      * rewrite HTE. unfold lp in Hx. lia.
      * rewrite (KOUT x ltac:(unfold lp, a5_buf, PF_O_BUF in *; lia) ltac:(unfold lp, a5_buf, PF_O_BUF in *; lia) Hne).
        apply (aview_some_of_apresent SEGS). apply HFP. unfold lp, a5_buf, PF_O_BUF in *. lia.
    + rewrite (KALL x ltac:(unfold lp, a5_buf, PF_O_BUF in *; lia)).
      * apply (aview_some_of_apresent SEGS). apply HFP. unfold lp, a5_buf, PF_O_BUF in *. lia.
      * unfold a5_Wrx. rewrite SPF. unfold lp, a5_buf, PF_O_BUF in *.
        intros [Hq | [Hq | [Hq | Hq]]]; [lia | destruct Hq as [Hq _]; discriminate Hq | lia |
          destruct Hq as [Hq _]; discriminate Hq]. }
assert (HINB : pf_inb (a5_buf v pos) lp (pf_tline (p_s v) o)).
{ rewrite HTLN. unfold pf_inb, lp. split; [lia|]. fold m. lia. }
(* the cut's remaining reader facts and registers *)
assert (HSL2 : pf_sl (rdW W2 mem2) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)]).
{ apply (a5_keep_slot v pos (rdW Wc memc) (rdW W2 mem2) false (pf_cur_ptr (p_c v) cur) G);
    [|exact HSL]. intros a Ha Hn. apply KALL; [exact Ha | exact Hn]. }
assert (HLN2 : a5_ln n v pos (rdW W2 mem2) cf cur nm o ln d).
{ pose proof HLN as (L1 & L2 & L3 & L4). split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  eapply (a5_keep_st B v pos lyc Sc Wc memc mdc W2 mem2); try eassumption. }
assert (HRG3 : pf_rg regs2 (PF_RL v pos ++ PF_RM v o ln ++ [(20, 0x20); (25, 9); (10, lp)])).
{ apply a5_rg_app. split.
  - apply (a5_rg_pres (ms_regs ms) regs2 _ HP2 (a5_RL_cs v pos)).
    unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?rr) = _ =>
        rewrite (QK rr ltac:(unfold a5c_keep; a5tr_in)); eapply a5_rg_get;
        [exact HRG | unfold PF_RL; a5tr_in] end.
  - apply a5_rg_app. split.
    + apply (a5_rg_pres (ms_regs ms) regs2 _ HP2 (a5_RM_cs v o ln)).
      unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        lazymatch goal with |- getr _ (Z_to_bv 5 ?rr) = _ =>
          rewrite (QK rr ltac:(unfold a5c_keep; a5tr_in)); eapply a5_rg_get;
          [exact HRG | unfold PF_RL, PF_RM; a5tr_in] end.
    + repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
      * rewrite (HP2 20 ltac:(unfold acallee_saved; lia)).
        rewrite (QK 20 ltac:(unfold a5c_keep; a5tr_in)). eapply a5_rg_get; [exact HRG | unfold PF_RL, PF_RM; a5tr_in].
      * rewrite (HP2 25 ltac:(unfold acallee_saved; lia)).
        apply (a5tr_rbv _ (25%bv) 25); [reflexivity | rewrite Q25; reflexivity].
      * apply (a5tr_rbv _ (10%bv) 10); [reflexivity | exact Ha0]. }
(* R5 *)
replace (BASE + 12820) with (BASE + A5_R5) by (unfold A5_R5, AF_reac_segconf_parse_file; lia).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A5_R5)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + A5_R5) regs2 mem2 md2).
apply (HR5 v pos lyc S2 W2 regs2 mem2 md2 cf cur nm o ln d lp).
split; [exact HB2|]. split; [exact HLN2|]. split; [exact HSL2|]. split; [unfold a5_len; lia|].
split; [exact HSTR2|]. split; [exact HINB | exact HRG3].
Qed.

(* ============================== R5 (0x87f48) -> TAIL / HDR / KEY ============================== *)
Lemma a5_r5_ok : forall n, H_TAIL B n -> H_HDR B n -> H_KEY B n -> H_R5 B n.
Proof.
intros n HTAIL HHDR HKEY v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp HI.
pose proof HI as (HB & HLN & HSL & HLT & HSTR & HINB & HRG).
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & HSHP).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (HCX & HJI & HOBJ & HSLL & HFSH).
pose proof HJI as (HJ & Hly0 & HSfs & HPerm0 & HSAV & HFL & HFRM & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (STKT & _ & _ & SPF & _).
pose proof alloc_ceiling_lt as HC.
destruct (a5tr_buf_rng v pos G) as (Hb0 & Hb1 & HF1 & HF2 & HF8).
destruct (a5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HNZ & HLSZ & _ & _ & _ & HCHEAP).
pose proof HLN as (HLC & HOLT & HREST & HST).
unfold a5_len in HLT.
pose proof HINB as (HI1 & HI2).
(* the byte at lp, the cur pointer in the slot *)
set (hd := hd0 (pf_tline (p_s v) o)) in *.
pose proof (a5tr_hd0_at _ lp _ HSTR) as HHD.
assert (HHDR0 : 0 <= hd <= 255) by (pose proof (sa_aview_rng _ _ _ _ _ HHD); lia).
assert (Hcpw : rdword (rdW Wc memc) (pf_s1 v + 0xb0) = Some (pf_cur_ptr (p_c v) cur))
  by (exact (proj1 (Forall_forall _ _) HSL (0xb0, pf_cur_ptr (p_c v) cur) ltac:(a5tr_in))).
pose proof (a5tr_rdword_rng (w_H Wc) memc _ _ Hcpw) as Hcprng.
assert (R10 : getr rX (Z_to_bv 5 10) = w64 lp)
  by (eapply a5_rg_get; [exact HRG | unfold PF_RL, PF_RM; a5tr_in]).
assert (Hlprng : a5_buf v pos <= lp < a5_buf v pos + 512) by (unfold pf_inb in HINB; lia).
(* the seed *)
pose proof (a5r_seed v pos lyc Sc Wc rX memc mdc lp (pf_cur_ptr (p_c v) cur) hd HB G R10 Hlprng HHD
  HHDR0 Hcpw Hcprng) as HS.
pose proof (a5r_E_img rX (pf_cur_ptr (p_c v) cur) hd) as HEI.
pose proof (a5r_E_agree rX (pf_cur_ptr (p_c v) cur) hd) as HA0.
assert (E10 : ew (a5r_E rX (pf_cur_ptr (p_c v) cur) hd) 10 = Z_to_bv 64 lp)
  by (rewrite (a5r_ew_reg rX _ hd 10 (Z_to_bv 5 10) eq_refl); exact R10).
assert (E22 : ew (a5r_E rX (pf_cur_ptr (p_c v) cur) hd) 22 = Z_to_bv 64 SHADOW_OFF).
{ rewrite (a5r_ew_reg rX _ hd 22 (Z_to_bv 5 22) eq_refl).
  eapply a5_rg_get; [exact HFI | unfold a5_FI; a5tr_in]. }
assert (E32 : ew (a5r_E rX (pf_cur_ptr (p_c v) cur) hd) 32 = Z_to_bv 64 (pf_cur_ptr (p_c v) cur))
  by apply a5r_ew_cp.
assert (E33 : ew (a5r_E rX (pf_cur_ptr (p_c v) cur) hd) 33 = Z_to_bv 64 hd) by apply a5r_ew_hd.
assert (SHOK : sh_ok SEGS a5_Bx [] (a5r_E rX (pf_cur_ptr (p_c v) cur) hd) (mrestrict (w_H Wc) memc))
  by constructor.
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF lp 1).
{ destruct (a5tr_addr_buf v pos lyc Sc Wc rX memc mdc lp 1 HB G ltac:(lia) ltac:(lia) ltac:(lia))
    as (_ & _ & _ & HQ & _). exact HQ. }
(* what every exit shares: the facts carried across a run that writes nothing *)
assert (EXIT : forall (rX' : bvmap 5 word) memc' mdc',
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall kk, In kk a5r_keep_t -> getr rX' (Z_to_bv 5 kk) = getr rX (Z_to_bv 5 kk)) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' PF_SC_LINE /\
  pf_sl (rdW Wc memc') (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] /\
  pf_st v pos (rdW Wc memc') cf cur nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc') lp (pf_tline (p_s v) o) /\
  pf_rg rX' (PF_RL v pos ++ PF_RM v o ln)).
{ intros rX' memc' mdc' HJ' HK' HV' HQK.
  assert (HRG' : pf_rg rX' (a5_FI B v)).
  { unfold pf_rg, a5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?rr) = _ =>
        rewrite (HQK rr ltac:(unfold a5r_keep_t; a5tr_in)); eapply a5_rg_get;
        [exact HFI | unfold a5_FI; a5tr_in] end. }
  split; [exact (a5tr_base_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE rX' memc' mdc' HB HJ'
    (fun a _ => HK' a) HV' HRG')|].
  split.
  { unfold pf_sl. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact Hcpw|].
    intros kk Hk0. apply HK'. }
  split.
  { pose proof HST as (S1 & S2 & (fb & Sf1 & Sf2) & S4). split.
    - destruct S1 as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
      intros i Hi. rewrite HK'.
      exact (Hbs i Hi).
    - split; [exact S2|]. split; [|exact S4]. exists fb. split; [|exact Sf2].
      intros i Hi. rewrite HK'. exact (Sf1 i Hi). }
  split.
  { pose proof HSTR as ((HZ1 & HZ2) & HZ3). split; [split|].
    - intros i Hi. rewrite HK'. exact (HZ1 i Hi).
    - exact HZ2.
    - intros x Hx. rewrite HK'. exact (HZ3 x Hx). }
  apply a5_rg_app. split.
  - unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?rr) = _ =>
        rewrite (HQK rr ltac:(unfold a5r_keep_t; a5tr_in)); eapply a5_rg_get;
        [exact HRG | unfold PF_RL; a5tr_in] end.
  - unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?rr) = _ =>
        rewrite (HQK rr ltac:(unfold a5r_keep_t; a5tr_in)); eapply a5_rg_get;
        [exact HRG | unfold PF_RL, PF_RM; a5tr_in] end. }
(* the post, by the line's step *)
rewrite (a5_post_step B v cf cur nm o ln HOLT).
rewrite (r_line_short cf cur nm (ln + 1) (p_s v) o ltac:(unfold a5_len in *; lia)).
fold hd.
pose proof (a5_mid n v pos (rdW Wc memc) cf cur nm o ln d HNZ HLN) as HMID.
revert HS HEI HA0 E10 E22 E32 E33 SHOK.
generalize (a5r_E rX (pf_cur_ptr (p_c v) cur) hd) as E0. intros E0 HS HEI HA0 E10 E22 E32 E33 SHOK.
unfold cfg_at. change (w64 (BASE + A5_R5)) with (Z_to_bv 64 (BASE + A5_R5)).
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KP : forall a, rdW Wc memc a <> None -> rdW Wc memc a <> None) by (intros; assumption).
(* 0x87f48 .. 0x87f60: check 7, the byte, `beqz a0` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold a5_Bx.
  rewrite (U_atom _ 22 SHADOW_OFF E22 ltac:(unfold SHADOW_OFF; lia)).
  rewrite (U_atom _ 10 lp E10 ltac:(lia)). exact HRA. }
{ a5tr_awr. }
a5tr_after E0 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the first byte is 0: the empty line, TAIL at the next line *)
  pose proof (a5tr_br_eq_lit _ 33 hd 0 _ (a5tr_ag_ew _ _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc)
    as Hz. apply Z.eqb_eq in Hz. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_TAIL.
  { a5tr_awr. }
  a5tr_after E0 HAE KM KP.
  pose proof (a5tr_regs_kept rX [w64 (pf_cur_ptr (p_c v) cur); w64 hd] _ _ _ _ a5r_keep_t HS
    (a5tr_ag32 rX _ E0 _ 34 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HQK.
  prreg HS (20%bv : bv 5) N20.
  first [rewrite (a5tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) in N20 | rewrite E32 in N20].
  pmkst HS.
  change (Z_to_bv 64 (BASE + PF_TAIL)) with (w64 (BASE + PF_TAIL)).
  lazymatch goal with |- SRr _ _ _ (pf_postm _ _ ?st _ _) =>
    assert (EQP : st = (cf, cur, nm)) by (rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity) end.
  rewrite EQP.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    destruct (EXIT rg mm mdn HJ (a5tr_keep_all Wc memc mm KM) (fun a Ha => KP a Ha) HQK)
      as (XB & XSL & XST & XSTR & XRG);
    apply (HTAIL v pos lyc Sc Wc rg mm mdn cf cur nm (pf_next (p_s v) o) (ln + 1)
      (d ++ [pf_line (p_s v) o])) end.
  split; [exact XB|].
  pose proof HMID as (_ & _ & HLC2).
  split; [exact HLC2|].
  split; [pose proof (pf_next_skipn_lt (p_s v) o HOLT); lia|].
  split.
  { pose proof XST as (T1 & T2 & T3 & T4). split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
    eapply pf_cnt_mono; [|exact T4]. pose proof (pf_next_skipn_lt (p_s v) o HOLT). lia. }
  apply a5_rg_app. split; [exact (proj1 (proj1 (a5_rg_app _ _ _) XRG))|].
  pose proof (proj2 (proj1 (a5_rg_app _ _ _) XRG)) as XRM.
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  + eapply a5_rg_get; [exact XRM | unfold PF_RM; a5tr_in].
  + eapply a5_rg_get; [exact XRM | unfold PF_RM; a5tr_in].
  + apply (a5tr_rbv _ (20%bv) 20); [reflexivity | rewrite N20; reflexivity].
- (* the first byte is not 0 *)
  pose proof (a5tr_br_eq_lit _ 33 hd 0 _ (a5tr_ag_ew _ _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc)
    as Hz. apply Z.eqb_neq in Hz. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { a5tr_awr. }
  a5tr_after E0 HAE KM KP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* not '[': KEY *)
    pose proof (a5tr_br_ne_lit _ 33 hd 0x5b _ (a5tr_ag_ew _ _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia)
      ltac:(lia) Hc) as Hk. apply negb_true_iff, Z.eqb_neq in Hk. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_KEY.
    { a5tr_awr. }
    a5tr_after E0 HAE KM KP.
    pose proof (a5tr_regs_kept rX [w64 (pf_cur_ptr (p_c v) cur); w64 hd] _ _ _ _ a5r_keep HS
      (a5tr_ag32 rX _ E0 _ 34 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HQK.
    pose proof (fun kk Hk0 => HQK kk (a5tr_keep_sub kk Hk0)) as HQKt.
    prreg HS (23%bv : bv 5) N23.
    first [rewrite (a5tr_ag_ew _ _ _ 10 _ HAE ltac:(lia) E10) in N23 | rewrite E10 in N23].
    pmkst HS.
    change (Z_to_bv 64 (BASE + PF_KEY)) with (w64 (BASE + PF_KEY)).
    lazymatch goal with |- SRr _ _ _ (pf_postm _ _ ?st _ _) =>
      assert (EQP : st = r_key cf cur nm (ln + 1) (pf_tline (p_s v) o))
        by (rewrite (proj2 (Z.eqb_neq _ _) Hz), (proj2 (Z.eqb_neq _ _) Hk); reflexivity) end.
    rewrite EQP.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      destruct (EXIT rg mm mdn HJ (a5tr_keep_all Wc memc mm KM) (fun a Ha => KP a Ha) HQKt)
        as (XB & XSL & XST & XSTR & XRG);
      apply (HKEY v pos lyc Sc Wc rg mm mdn cf cur nm o ln (d ++ [pf_line (p_s v) o]) lp) end.
    split; [exact XB|]. split; [exact HMID|]. split; [exact XST|]. split; [exact XSL|].
    split; [unfold a5_len in *; lia|]. split; [exact XSTR|].
    split; [unfold a5_buf in XB |- *; exact HINB|].
    split; [exact Hz|]. split; [exact Hk|].
    apply a5_rg_app. split; [exact (proj1 (proj1 (a5_rg_app _ _ _) XRG))|].
    apply a5_rg_app. split; [exact (proj2 (proj1 (a5_rg_app _ _ _) XRG))|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    * rewrite (HQK 20 ltac:(unfold a5r_keep; a5tr_in)). eapply a5_rg_get; [exact HRG | unfold PF_RL, PF_RM; a5tr_in].
    * rewrite (HQK 25 ltac:(unfold a5r_keep; a5tr_in)). eapply a5_rg_get; [exact HRG | unfold PF_RL, PF_RM; a5tr_in].
    * apply (a5tr_rbv _ (23%bv) 23); [reflexivity | rewrite N23; reflexivity].
  + (* '[': HDR *)
    pose proof (a5tr_br_ne_lit _ 33 hd 0x5b _ (a5tr_ag_ew _ _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia)
      ltac:(lia) Hc) as Hk. apply negb_false_iff, Z.eqb_eq in Hk. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_HDR.
    { a5tr_awr. }
    a5tr_after E0 HAE KM KP.
    pose proof (a5tr_regs_kept rX [w64 (pf_cur_ptr (p_c v) cur); w64 hd] _ _ _ _ a5r_keep HS
      (a5tr_ag32 rX _ E0 _ 34 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HQK.
    pose proof (fun kk Hk0 => HQK kk (a5tr_keep_sub kk Hk0)) as HQKt.
    prreg HS (23%bv : bv 5) N23.
    first [rewrite (a5tr_ag_ew _ _ _ 10 _ HAE ltac:(lia) E10) in N23 | rewrite E10 in N23].
    pmkst HS.
    change (Z_to_bv 64 (BASE + PF_HDR)) with (w64 (BASE + PF_HDR)).
    lazymatch goal with |- SRr _ _ _ (pf_postm _ _ ?st _ _) =>
      assert (EQP : st = r_header cf nm (ln + 1) (pf_tline (p_s v) o))
        by (rewrite (proj2 (Z.eqb_neq _ _) Hz), (proj2 (Z.eqb_eq _ _) Hk); reflexivity) end.
    rewrite EQP.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      destruct (EXIT rg mm mdn HJ (a5tr_keep_all Wc memc mm KM) (fun a Ha => KP a Ha) HQKt)
        as (XB & XSL & XST & XSTR & XRG);
      apply (HHDR v pos lyc Sc Wc rg mm mdn cf cur nm o ln (d ++ [pf_line (p_s v) o]) lp) end.
    split; [exact XB|]. split; [exact HMID|]. split; [exact XST|]. split; [exact XSL|].
    split; [unfold a5_len in *; lia|]. split; [exact XSTR|].
    split; [unfold a5_buf in XB |- *; exact HINB|].
    split; [exact Hk|].
    apply a5_rg_app. split; [exact (proj1 (proj1 (a5_rg_app _ _ _) XRG))|].
    apply a5_rg_app. split; [exact (proj2 (proj1 (a5_rg_app _ _ _) XRG))|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    * rewrite (HQK 20 ltac:(unfold a5r_keep; a5tr_in)). eapply a5_rg_get; [exact HRG | unfold PF_RL, PF_RM; a5tr_in].
    * rewrite (HQK 25 ltac:(unfold a5r_keep; a5tr_in)). eapply a5_rg_get; [exact HRG | unfold PF_RL, PF_RM; a5tr_in].
    * apply (a5tr_rbv _ (23%bv) 23); [reflexivity | rewrite N23; reflexivity].
Qed.

End e.
End f.
End d.
