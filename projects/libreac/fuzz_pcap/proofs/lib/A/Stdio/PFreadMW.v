(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the walk of musl's fread inside libreac/fuzz_pcap (libreac v1.9.0,
   memory-checking build). frd_walk proves lib/A/Stdio/PFreadM.v's rfread_contract (the
   caller-journal form of a working branch 9b4de8c19fc) from its three callees, taken
   as Section hypotheses: the memory-copy trampoline's aintrin_realizes OCpy (cgif YG0d.v:317-335),
   rtoread_contract and rmread_contract (PFreadM.v; their proofs are the sibling lanes'). The
   instances are in their own files: rfread_contract_asan in lib/A/Stdio/PFreadMWA.v and
   rfread_contract_asan_ubsan in lib/B/Stdio/PFreadMWB.v. This file Requires no image, no image's
   pc file and no lib/A/Prog file that names an image (YC85G, not YC85).

   IMAGE-GENERIC. Nothing in frd_walk names an address of one image. The entry pc, the two callee
   entries and the memory-copy trampoline are parameters; the instruction words come from one
   position-abstract listing (frd_listing) whose certificate pi_check is a Section hypothesis, as
   in the donor's per-function walks. The two instances discharge it by computation
   (frd_cert_asan, frd_cert_asan_ubsan): the 79 words are the same in both images except the
   memory-copy jal, which is a PCall in the listing.

   THE CODE, read off the ORIGINAL v1.9.0
   pinned fuzz_pcap.asan image (sha256 b7a91d9b1fb0; symbols from the unstripped
   twin fuzz_pcap.asan (sha256 36da3052c383)): fread 0x8ee5c, 316 bytes = 79 instruction words,
   frame 64. The two calls the walk composes are slot 33 (0x8eee0, the memory-copy trampoline)
   and slot 41 (0x8ef00, __toread); the indirect call at slot 47 (0x8ef18, `jalr a3`) goes to
   f->read = mread. The four calls of __lockfile / __unlockfile (0x8ee9c, 0x8ef44, 0x8ef58) are
   never reached (the lock word +140 is -1 and s5 = 1), so their words stay plain words.

   THE LOOP DOES NOT NEED INDUCTION. mread sets F_EOF exactly when the request exceeds what is
   left (rmread_post), and __toread returns -1 on F_EOF (rtoread_post), so the back edge at
   0x8ef28 is taken at most once and the second __toread call leaves the loop. The walk is a
   finite enumeration of eight paths. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal YC85G.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM PSourceFrame PFreadArith PFreadCall PFreadPost.
Import ListNotations.
(* lia guard: the Zify flag leak at YE2e.v:29 / AE2e.v:30 (~120 files) sets the euclidean-division flag to false globally *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The names fread's listing calls. *)
Inductive fsym : Type := FS_memcpy | FS_toread.

Definition A_LIMF : nat := 512%nat.
Lemma A_LIMF_text : (A_TEXT < A_LIMF)%nat.
Proof. unfold A_TEXT, A_LIMF. lia. Qed.
Definition frd_listing : ptable fsym := [
PW 0xfc010113;
PW 0x2113c23;
PW 0x2813823;
PW 0x2913423;
PW 0x3213023;
PW 0x1313c23;
PW 0x1413823;
PW 0x1513423;
PW 0x1613023;
PW 0x68413;
PW 0x60913;
PW 0x58493;
PW 0x8c6a583;
PW 0x50993;
PW 0x5ca63;
PW 0x40513;
PW 0xc44ff0ef;
PW 0x153a93;
PW 0x80006f;
PW 0x100a93;
PW 0x8842603;
PW 0x843583;
PW 0x1043503;
PW 0xfff60693;
PW 0xc6e633;
PW 0x8c42423;
PW 0x2990b33;
PW 0xca58263;
PW 0x40b50a33;
PW 0x16a6463;
PW 0xb0a13;
PW 0x98513;
PW 0xa0613;
PCall FS_memcpy (1%bv : bv 5);
PW 0x843503;
PW 0x14989b3;
PW 0x1450533;
PW 0xa43423;
PW 0x414b0a33;
PW 0x20a0a63;
PW 0x40513;
PCall FS_toread (1%bv : bv 5);
PW 0x4051663;
PW 0x4043683;
PW 0x40513;
PW 0x98593;
PW 0xa0613;
PW 0x680e7;
PW 0x2050a63;
PW 0x40aa0a33;
PW 0xa989b3;
PW 0xfc0a1ae3;
PW 0x14b513;
PW 0xfff50513;
PW 0x1257533;
PW 0x20a9663;
PW 0x50493;
PW 0x40513;
PW 0xc98ff0ef;
PW 0x48513;
PW 0x180006f;
PW 0xa9663;
PW 0x40513;
PW 0xc84ff0ef;
PW 0x414b0533;
PW 0x2955533;
PW 0x3813083;
PW 0x3013403;
PW 0x2813483;
PW 0x2013903;
PW 0x1813983;
PW 0x1013a03;
PW 0x813a83;
PW 0x13b03;
PW 0x4010113;
PW 0x8067;
PW 0xb0a13;
PW 0xf60b16e3;
PW 0xf99ff06f].

(* ---------------------------------------------------------------------- *)
(* The position-abstract walk helpers, as lib/A/Prog/PcapPaLib.v states    *)
(* them for pcap's own program listing, but over a listing and an image    *)
(* given as Section parameters, because musl's fread is not in that        *)
(* listing and the statement must hold of both images.                     *)
(* ---------------------------------------------------------------------- *)
Definition Eimg (val : nat -> Z) (E : env) : env :=
  {| ew := fun n => if ((A_TEXT <=? n) && (n <? A_LIMF))%nat then Z_to_bv 64 (val n) else ew E n; ed := ed E |}.
Lemma Eimg_low : forall val E n, (n < A_TEXT)%nat -> ew (Eimg val E) n = ew E n.
Proof. intros val E n Hn. cbn [Eimg ew]. replace (A_TEXT <=? n)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity. Qed.
Lemma Eimg_env : forall val E, (forall a, 0 <= val a < 2 ^ 64) -> PaRun.img_env val A_LIMF (Eimg val E).
Proof.
intros val E Hvr a [H1 H2]. cbn [Eimg ew]. replace ((A_TEXT <=? a) && (a <? A_LIMF))%nat%bool with true.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. pose proof (Hvr a). change (bv_modulus 64) with (2 ^ 64). lia.
- symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia].
Qed.
Lemma fr_base_reg : forall vl regs extra (n : nat) (r : bv 5),
  Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat ->
  base_val (Eimg vl (Ereg regs extra)) (Some n) = bv_unsigned (getr regs r).
Proof.
intros vl regs extra n r Hn Hlt. cbn [base_val]. rewrite Eimg_low by exact Hlt.
rewrite (ew_Ereg_nat regs extra n r Hn). reflexivity.
Qed.
Lemma fr_regs_ok : forall val regs extra, regs_ok (Eimg val (Ereg regs extra)) sr_atoms regs.
Proof.
intros. apply (regs_ok_agree 32 (Ereg regs extra)).
- split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma fr_codeptr_val : forall val E k, PaRun.img_env val A_LIMF E -> sv_denot E (SOff A_TEXT k) = Z_to_bv 64 (val A_TEXT + k).
Proof. intros val E k HE. cbn [sv_denot]. rewrite (HE A_TEXT (conj (le_n A_TEXT) A_LIMF_text)). reflexivity. Qed.
Lemma fr_img_codeptr : forall val E, PaRun.img_env val A_LIMF E -> forall k, Z_to_bv 64 (bv_unsigned (ew E 240%nat) + k) = Z_to_bv 64 (val A_TEXT + k).
Proof. intros val E HE k. pose proof (HE A_TEXT (conj (le_n A_TEXT) A_LIMF_text)) as H. cbv [A_TEXT] in H. rewrite H. reflexivity. Qed.
Lemma fr_ew_havoc_above : forall E k ws i, (k + length ws <= i)%nat -> ew (havoc E k ws) i = ew E i.
Proof.
intros E k ws i Hi. unfold havoc. cbn [ew]. destruct (i <? k)%nat eqn:Hlt; [reflexivity|]. apply nth_overflow. lia.
Qed.
Lemma fr_img_env_havoc : forall val E k ws, PaRun.img_env val A_LIMF E -> (k + length ws <= A_TEXT)%nat -> PaRun.img_env val A_LIMF (havoc E k ws).
Proof. intros val E k ws HE Hk a Ha. rewrite fr_ew_havoc_above by lia. exact (HE a Ha). Qed.

(* lib/A/Prog/YC4b.v's kept_of_frame, restated here so this file does not need YC4b. *)
Lemma fr_kept_of_frame {fx : YK11.FPState} : forall (segs : list Segment) E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs H m' a = aview segs H m a.
Proof.
intros segs E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of segs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.

Lemma fr_env_agree : forall vl regs extra, env_agree 32 (Ereg regs extra) (Eimg vl (Ereg regs extra)).
Proof. intros vl regs extra. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Section help. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Variable val : nat -> Z.
Variable sigma : fsym -> Z.
Variable listing : ptable fsym.
Hypothesis Hcert : pi_check fsym (clookup tbl) val sigma listing = true.
Hypothesis HBok : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Hypothesis Hvalrange : forall a, 0 <= val a < 2 ^ 64.
Hypothesis Hlim : forallb (pinstr_atoms_ltb A_LIMF) listing = true.
Hypothesis Hlen : 4 * Z.of_nat (length listing) <= 2 ^ 40.
#[local] Notation BASE := (val A_TEXT).
#[local] Notation tpi := (ptree_of_list listing).
#[local] Notation tw := (tw_of 0 listing).
#[local] Notation img_env := (img_env val A_LIMF).
#[local] Notation st_ok_pi := (st_ok_pi segs val).

Lemma fr_fetch_ok : forall pc w, clookup tbl pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Proof. intros pc w H. exact (tbl_ok pc w H). Qed.

Definition fr_run := SRr_run_pi_tok_AJ fsym segs B LAWS segs_low Hwx (clookup tbl) val sigma listing
  tpi tw fr_fetch_ok Hcert HBok A_LIMF A_LIMF_text Hlim Hlen eq_refl eq_refl.
Definition fr_run_to := SRr_run_to_pi_tok_AJ fsym segs B LAWS segs_low Hwx (clookup tbl) val sigma listing
  tpi tw fr_fetch_ok Hcert HBok A_LIMF A_LIMF_text Hlim Hlen eq_refl eq_refl.

Lemma fr_branch : forall W E ss ms md Q c a b,
  st_ok_pi E ss (restrict (w_H W) ms) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = true -> st_ok_pi E (add_cond ss (mkAC c a b)) (restrict (w_H W) ms) -> SRr segs W (mkCfg ms md) Q) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = false -> st_ok_pi E (add_cond ss (mkAC (neg_bc c) a b)) (restrict (w_H W) ms) -> SRr segs W (mkCfg ms md) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof. exact (SRr_sym_branch_pi segs val). Qed.

Lemma fr_entry_st_ok : forall E pc sr regs (rs : smem) (G : facts) mem,
  regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok segs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
  st_ok_pi E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold PaRun.st_ok_pi, abs_ss, setpc, st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma fr_reg : forall (H : word -> bool) E ss ms r,
  st_ok_pi E ss (restrict H ms) -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros H E ss ms r HS. exact (st_ok_restrict_reg segs H E (abs_ss val ss) ms r HS). Qed.
Lemma fr_mkst : forall (H : word -> bool) E ss ms,
  st_ok_pi E ss (restrict H ms) -> ss_resv ss = None ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (ms_mem ms) (seg_rom segs).
Proof. intros H E ss ms HS Hrv. exact (st_ok_restrict_mkst segs H E (abs_ss val ss) ms HS ltac:(destruct ss; exact Hrv)). Qed.

Lemma fr_lookup_pw : forall k w, plookup tpi k = Some (PW w) -> clookup tbl (BASE + k) = Some w /\ 0 <= k /\ k mod 4 = 0.
Proof.
intros k w Hpl.
pose proof (cert_slot fsym (clookup tbl) val sigma listing Hcert _ _ Hpl) as (Hck & Hk0 & Hk4). unfold pi_slot_check in Hck.
destruct (clookup tbl (BASE + k)) as [wz|] eqn:Hl; [|discriminate Hck]. apply Z.eqb_eq in Hck. subst wz. auto.
Qed.
Lemma fr_ret_at : forall W E ss ms md Q,
  st_ok_pi E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  plookup tpi (ss_pc ss) = Some (PW RET_WORD_r) ->
  (forall mat', Q W (mkCfg (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom segs))
     (with_vm_backing (m_vm_lazy md) mat' md))) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
intros W E ss ms md Q HS Hrv Hpl HQ.
pose proof (fr_lookup_pw _ _ Hpl) as (Hl & _ & _).
apply (SRr_ret_at segs tbl tbl_ok Hwx W E (abs_ss val ss) ms md Q HS); [destruct ss; exact Hrv | exact Hl | exact HQ].
Qed.
Theorem fr_after_call : forall k E ss ms regs' mem' rs retk,
  img_env E -> 0 <= retk < 2 ^ 40 ->
  st_ok segs E ss ms ->
  ss_resv ss = None ->
  (k + 16 <= A_TEXT)%nat ->
  ss_atoms_p (pband k A_TEXT) ss = true ->
  regions_wf rs = true -> no_cdata rs = true -> mem_atoms_p (pband k A_TEXT) rs = true ->
  submem rs (ss_mem ss) ->
  sr_get (ss_regs ss) 1 = SOff A_TEXT retk ->
  aregs_preserved (ms_regs ms) regs' ->
  Forall (region_kept segs E (ms_mem ms) mem') rs ->
  st_ok_pi (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retk)
    (mkst regs' (Z_to_bv 64 (BASE + retk)) mem' (seg_rom segs)).
Proof.
intros k E ss ms regs' mem' rs retk HE Hrk HS Hrv Hk Hat Hwf Hnc Hmat Hsub Hra HP Hkept.
unfold PaRun.st_ok_pi, abs_ss, ss_after_call, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape. rewrite Hshape in HS.
pose proof (st_ok_splice_havoc_p segs k A_TEXT E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) (BASE + retk)
(ms_mem ms) mem' rs [] CLOB HS Hk Hat) as H.
cbn [map app] in H. apply H.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact Hmat.
- apply regs_preserved_frame. exact HP.
- constructor.
- apply (mem_ok_kept segs E (ms_mem ms) mem' rs); [| exact Hnc | exact Hkept].
  eapply mem_ok_sub; [exact Hsub | exact Hwf | exact (st_ok_mem_ok segs E ss _ HS)].
Qed.
Lemma fr_jalr_entry : forall (H : word -> bool) E ss ms (rd : bv 5) tgt,
  img_env E -> st_ok_pi E ss (restrict H ms) -> ss_resv ss = None -> bv_eqb rd 0 = false ->
  0 <= ss_pc ss + 4 < 2 ^ 40 ->
  st_ok segs E (mkSST tgt (sr_set (ss_regs ss) rd (SOff A_TEXT (ss_pc ss + 4))) (ss_fregs ss) (ss_mem ss) None (ss_facts ss))
    (restrict H (mkst (regupd (ms_regs ms) rd (Z_to_bv 64 (BASE + (ss_pc ss + 4)))) (Z_to_bv 64 tgt) (ms_mem ms) (seg_rom segs))).
Proof.
intros H E ss ms rd tgt HEI HS Hrv Hrd Hk. rewrite restrict_mkst_fx.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold abs_ss, setpc in H4, H7, H8, H9. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in H4, H7, H8, H9.
rewrite Hrv in H4.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst restrict
ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
cbn [restrict ms_fregs ms_fcsr ms_regs ms_mem] in H2, H5, H7, H8, H9.
do 6 (split; [first [reflexivity | assumption] |]).
split; [| exact (conj H8 H9)].
pose proof (regs_ok_set E (ss_regs ss) (ms_regs ms) rd (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (SOff A_TEXT (ss_pc ss + 4)) H7) as R.
rewrite Hrd in R. apply R. exact (fr_codeptr_val val E (ss_pc ss + 4) HEI).
Qed.
Lemma fr_v_jalr_lit_even : forall tgt, 0 <= tgt < 2 ^ 64 -> tgt mod 2 = 0 -> v_jalr (Z_to_bv 64 tgt) 0 = Z_to_bv 64 tgt.
Proof.
intros tgt Ht He. unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite YK0s.land_m2_even by exact He. reflexivity.
Qed.
Lemma fr_jalr_call : forall W E ss ms md Q w (rd rs1 : bv 5) tgt,
  img_env E -> st_ok_pi E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  plookup tpi (ss_pc ss) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Jalr rd rs1 0%bv, 4%Z) -> bv_eqb rd 0 = false ->
  ss_pc ss + 4 < 2 ^ 40 ->
  getr (ms_regs ms) rs1 = Z_to_bv 64 tgt -> 0 <= tgt < 2 ^ 64 -> tgt mod 2 = 0 ->
  (forall mat' ms1,
     ms1 = mkst (regupd (ms_regs ms) rd (Z_to_bv 64 (BASE + (ss_pc ss + 4)))) (Z_to_bv 64 tgt) (ms_mem ms) (seg_rom segs) ->
     st_ok segs E (mkSST tgt (sr_set (ss_regs ss) rd (SOff A_TEXT (ss_pc ss + 4))) (ss_fregs ss) (ss_mem ss) None (ss_facts ss))
       (restrict (w_H W) ms1) ->
     SRr segs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
intros W E ss ms md Q w rd rs1 tgt HEI HS Hrv Hpc Hdec Hrd Hk Hrs1 Htgt Heven HK.
pose proof HBok as (HB0 & HB1 & _).
pose proof (fr_lookup_pw _ _ Hpc) as (Hl & Hk0 & _).
pose proof (fr_mkst (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hshape at 1.
eapply (SRr_step segs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  eapply (step_jalr_link segs _ _ _ _ (Z_to_bv 32 w) rd rs1 (0%bv : bv 12) (Z_to_bv 64 tgt)).
  + exact (fr_fetch_ok _ _ Hl).
  + eapply not_ecall_of_decode; [exact Hdec | discriminate].
  + exact Hdec.
  + exact Hrd.
  + cbn [ms_regs mkst]. exact Hrs1.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  change (bv_signed (0%bv : bv 12)) with 0. rewrite (fr_v_jalr_lit_even tgt Htgt Heven).
  unfold v_addi. rewrite unsigned_lit_small by (clear - HB0 HB1 Hk0 Hk; lia).
  replace (BASE + ss_pc ss + 4) with (BASE + (ss_pc ss + 4)) by (clear; lia).
  eapply HK; [reflexivity|].
  exact (fr_jalr_entry (w_H W) E ss ms rd tgt HEI HS Hrv Hrd ltac:(clear - Hk0 Hk; lia)).
Qed.
Lemma fr_add_region : forall E ss ms r,
  st_ok_pi E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
  st_ok_pi E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms r HS Hw Hr Hd. exact (ast_ok_add_region segs E (abs_ss val ss) ms r HS Hw Hr Hd). Qed.
Lemma fr_ret_of_ok : forall (x : word), YK0s.ret_ok x -> v_jalr x 0 = x.
Proof. intros x H. exact H. Qed.
Lemma fr_call : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
  (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre segs B STK1 lyc Sc W regsc memc mdc ch1 ->
   SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
     (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
        c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
        ajournal segs B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
        aregs_preserved regsc regs2 /\ Q ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
       ajournal segs B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
       aregs_preserved regsc regs2 /\ Q ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 Q
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_tok segs B LAWS segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End help.

(* The tactics of lib/A/Prog/PcapPaLib.v, over fr_run / A_LIMF. *)
Ltac frd_after_run HS HJ SHOK :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in let HEI := fresh "HEI" in
intros ws ms' mat' Hlen HEI HS SHOK HJ HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK, HEI;
cbn [ms_mem mkst] in HF, HFr, HG, HJ;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac frd_run RUN HS HJ SHOK :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K A_LIMF Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok (ptree_of_list frd_listing) (tw_of 0 frd_listing) K Bx (0, 0) SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok (ptree_of_list frd_listing) (tw_of 0 frd_listing) K Bx (0, 0) SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : PaRun.img_env _ _ E |- _ => HEI | _ => fail "frd_run: no img_env hypothesis" end in
eapply (RUN W FUEL E K Bx (0, 0) SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(unfold A_LIMF; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
frd_after_run HS HJ SHOK ]
end end
end.
Ltac frd_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (fr_reg segs val H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Ltac frd_branch_auto :=
lazymatch goal with
| HS : st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) |- _ =>
  let KK := eval vm_compute in (run_K A_LIMF (SLit 0) (@nil shent) ss) in
  let r := eval vm_compute in (sym_step_pi_tok (ptree_of_list frd_listing) (tw_of 0 frd_listing) KK (SLit 0) (0, 0) (@nil shent)
    (start KK (SLit 0) (0, 0) (@nil shent) ss)) in
  lazymatch r with
  | PTStop (SR_branch ?c ?a ?b) => apply (fr_branch segs val W E ss ms _ _ c a b HS)
  | ?x => fail "frd_branch_auto: not stuck at a branch:" x
  end
end.

Lemma frd_lim : forallb (pinstr_atoms_ltb A_LIMF) frd_listing = true.
Proof. vm_compute. reflexivity. Qed.
Lemma frd_len : 4 * Z.of_nat (length frd_listing) <= 2 ^ 40.
Proof. vm_compute. discriminate. Qed.

(* The symbolic memory the walk starts from: fread's own 64-byte frame and the FILE block,
   with the five cells the body reads (rpos +8, rend +16, read +64, the orientation word +136
   and the lock word +140). The FILE's writable window is [+8, +140): the walk stores rpos
   (0x8eef0) and the orientation word (0x8eec0) and nothing else of its own. *)
Definition frd_stkR : YP09.region := YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 [].
(* Two regions, because fread writes two cells of the FILE that are not neighbours: rpos at +8
   (0x8eef0) and the orientation word at +136 (0x8eec0). A region has one write window, so a
   single [+8, +140) window would let the walk lose every FILE cell between them -- and
   asource_at names +24, +32..+56, +88, +96, +104, +112, +120 among them. *)
Definition frd_fileR1 : YP09.region := YP09.mkRegion (Some 13%nat) 0 136 8 16
  [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
   YP09.mkChunk 64 (CVal 8 (SOff 34 0))].
Definition frd_fileR2 : YP09.region := YP09.mkRegion (Some 13%nat) 136 1304 136 140
  [YP09.mkChunk 136 (CVal 4 (SOff 35 0)); YP09.mkChunk 140 (CVal 4 (SLit U32M1))].
Definition frd_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (13%nat, mkAF 4096 (2 ^ 47) 4);
           (12%nat, mkAF 0 (2 ^ 26) 0); (11%nat, mkAF 1 1 0); (10%nat, mkAF 0 (2 ^ 47) 0);
           (35%nat, mkAF 0 U32M1 0)] [] [].
Definition frd_ss0 : sstate := mkSS 0 sr_atoms [frd_stkR; frd_fileR1; frd_fileR2] None frd_facts.

Section walk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable K : asource_syms.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Variable val : nat -> Z.
Variable sigma : fsym -> Z.
Hypothesis Hcert : pi_check fsym (clookup tbl) val sigma frd_listing = true.
Hypothesis HBok : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Hypothesis Hvalrange : forall a, 0 <= val a < 2 ^ 64.
Hypothesis Hbase_lo : 4096 <= val A_TEXT.
(* The image fact the walk needs beside the listing: mread's entry (the value f->read holds,
   0x8ea40 on the asan pin) is an even address in range. *)
Hypothesis Hmread_pc : 0 <= as_read K < 2 ^ 64 /\ as_read K mod 2 = 0.
(* the read stream's image laws (PSourceMeta.v): its environment cells and the open-file-list head
   are image bytes, so a walk that writes only its frame and the FILE keeps them *)
Hypothesis ASIL : asource_img_laws SK segs B K.
(* The three callees, as Section hypotheses: their proofs are the sibling lanes'. *)
Hypothesis HMEMCPY : aintrin_realizes segs B OCpy (sigma FS_memcpy).
Hypothesis HTOREAD : rtoread_contract segs B K (sigma FS_toread).
Hypothesis HMREAD : rmread_contract segs B K (as_read K).
#[local] Notation BASE := (val A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
#[local] Notation EV regs extra := (Eimg val (Ereg regs extra)).

Lemma frd_entry : forall (W : world segs) lyc Sc (regs : bvmap 5 word) memc mdc (d nm f rp re mdv : Z),
  AR segs B lyc Sc W memc mdc ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 1 -> getr regs 12 = w64 nm -> getr regs 13 = w64 f ->
  spZ regs mod 16 = 0 -> 2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 ->
  (forall a, spZ regs - 64 <= a < spZ regs -> apresent (w_H W) memc a) ->
  f + SRC_FILE_BLOCK <= spZ regs - 64 ->
  val_mem segs (rd W memc) (f + 8) 8 rp ->
  val_mem segs (rd W memc) (f + 16) 8 re ->
  val_mem segs (rd W memc) (f + 64) 8 (as_read K) ->
  val_mem segs (rd W memc) (f + 136) 4 mdv ->
  val_mem segs (rd W memc) (f + 140) 4 U32M1 ->
  0 <= rp < 2 ^ 64 -> 0 <= re < 2 ^ 64 -> 0 <= mdv <= U32M1 -> 0 <= as_read K < 2 ^ 64 ->
  0 <= nm <= 2 ^ 26 -> 0 <= d -> d + nm <= 2 ^ 47 ->
  st_ok_pi segs val (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) frd_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0)) memc (seg_rom segs))).
Proof.
intros W lyc Sc regs memc mdc d nm f rp re mdv HAR Hblk G10 G11 G12 G13
  Hal16 Hsplo Hsphi Hpres Hfstk M8 M16 M64 M136 M140 Hrp Hre Hmd Hrdk Hnm Hd0 Hdhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK HAR Hblk)
  as (Hf16 & Hf0 & Hfceil & Hfapp & Hfbytes & Hfdisj & Hfrange).
assert (RQ : req_size SRC_FILE_BLOCK = SRC_FILE_BLOCK) by reflexivity. rewrite RQ in *.
set (E := EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]).
assert (HE2 : ew E 2 = getr regs 2).
{ subst E. rewrite (Eimg_low val (Ereg regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 2%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_nat regs _ 2 2%bv eq_refl). }
assert (HE10 : ew E 10 = w64 d).
{ subst E. rewrite (Eimg_low val _ 10%nat ltac:(cbv [A_TEXT]; lia)). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact G10. }
assert (HE11 : ew E 11 = w64 1).
{ subst E. rewrite (Eimg_low val _ 11%nat ltac:(cbv [A_TEXT]; lia)). rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl). exact G11. }
assert (HE12 : ew E 12 = w64 nm).
{ subst E. rewrite (Eimg_low val _ 12%nat ltac:(cbv [A_TEXT]; lia)). rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl). exact G12. }
assert (HE13 : ew E 13 = w64 f).
{ subst E. rewrite (Eimg_low val _ 13%nat ltac:(cbv [A_TEXT]; lia)). rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl). exact G13. }
assert (HE32 : ew E 32 = w64 rp).
{ subst E. rewrite (Eimg_low val _ 32%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_extra regs _ 0). }
assert (HE33 : ew E 33 = w64 re).
{ subst E. rewrite (Eimg_low val _ 33%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_extra regs _ 1). }
assert (HE34 : ew E 34 = w64 (as_read K)).
{ subst E. rewrite (Eimg_low val _ 34%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_extra regs _ 2). }
assert (HE35 : ew E 35 = w64 mdv).
{ subst E. rewrite (Eimg_low val _ 35%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_extra regs _ 3). }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite HE2; reflexivity).
assert (Uf : bv_unsigned (ew E 13) = f) by (rewrite HE13; unfold w64; apply unsigned_lit_small; lia).
assert (VB2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
assert (VB13 : base_val E (Some 13%nat) = f) by (cbn [base_val]; exact Uf).
assert (HRO : regs_ok E sr_atoms regs) by (subst E; apply fr_regs_ok).
clearbody E.
replace (BASE + 0) with (BASE + ss_pc frd_ss0) by (cbn; lia).
rewrite restrict_mkst_fx.
apply (fr_entry_st_ok segs val).
- exact HRO.
- vm_compute. reflexivity.
- unfold frd_ss0, frd_stkR, frd_fileR1, frd_fileR2. cbn [ss_mem].
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite VB2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + rewrite VB13. split; [lia|]. split; [change SRC_FILE_BLOCK with 1304 in *; lia|]. split.
    { intros o Ho. apply (apresent_writable segs). apply (proj1 (Hfbytes (f + o) ltac:(change SRC_FILE_BLOCK with 1304 in *; lia))). }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val segs E _ f 8 8%N (SOff 32 0) rp);
      [cbn [sv_denot]; rewrite HE32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact M8].
    * apply (chunk_ok_val segs E _ f 16 8%N (SOff 33 0) re);
      [cbn [sv_denot]; rewrite HE33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact M16].
    * apply (chunk_ok_val segs E _ f 64 8%N (SOff 34 0) (as_read K));
      [cbn [sv_denot]; rewrite HE34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact M64].
  + rewrite VB13. split; [lia|]. split; [change SRC_FILE_BLOCK with 1304 in *; lia|]. split.
    { intros o Ho. apply (apresent_writable segs). apply (proj1 (Hfbytes (f + o) ltac:(change SRC_FILE_BLOCK with 1304 in *; lia))). }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val segs E _ f 136 4%N (SOff 35 0) mdv);
      [cbn [sv_denot]; rewrite HE35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold U32M1 in Hmd; cbn; lia | cbn; lia | exact M136].
    * apply (chunk_ok_val segs E _ f 140 4%N (SLit U32M1) U32M1);
      [reflexivity | unfold U32M1; cbn; lia | cbn; lia | exact M140].
- unfold frd_ss0, frd_stkR, frd_fileR1, frd_fileR2. cbn [ss_mem]. cbn [pairwise_disjoint all_disjoint].
  change SRC_FILE_BLOCK with 1304 in *.
  repeat apply conj; try exact I;
  (unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?VB2, ?VB13;
   first [right; lia | left; lia]).
- unfold frd_ss0, frd_facts. cbn [ss_facts]. unfold facts_ok. cbn [f_atoms f_conds f_alias].
  cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite HE10, HE11, HE12, HE35, Usp, Uf.
  unfold w64. rewrite !unsigned_lit_small by (unfold U32M1 in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.


(* ---------------------------------------------------------------------- *)
(* The control flow of the walk, as facts about the listing (so they hold  *)
(* of every image whose pi_check certificate the instance supplies). Each  *)
(* is the symbolic engine's own run, checked by computation. FUEL is       *)
(* YP03's 200000; every run below stops long before it.                    *)
(* ---------------------------------------------------------------------- *)
Definition frd_K : nat := 512%nat.
Lemma frd_K_ok : run_K A_LIMF (SLit 0) [] frd_ss0 = frd_K.
Proof. vm_compute. reflexivity. Qed.
Definition frd_RUN (ss : sstate) : shst * ptrun_status fsym :=
  sym_runN_pi_tok (ptree_of_list frd_listing) (tw_of 0 frd_listing) frd_K (SLit 0) (0, 0) [] FUEL ss.
Definition frd_stop (ss : sstate) : sstate := sh_ss (fst (frd_RUN ss)).
Definition frd_with (c : branch_cond) (a b : sv) (ss : sstate) : sstate := add_cond ss (mkAC c a b).
(* the three symbolic values the walk branches on: rpos, rend, and size * nmemb *)
Definition SV_rpos : sv := SOff 32 0.
Definition SV_rend : sv := SOff 33 0.
Definition SV_total : sv := SMd M_MUL (SOff 12 0) (SOff 11 0).
Definition SV_win : sv := SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0).

(* 0x8ee5c-0x8eec8: the prologue, the lock test (+140 = -1, so __lockfile is skipped and s5 = 1),
   the orientation word |= word - 1 at +136, size * nmemb, and the window test `beq rpos, rend`. *)
Lemma frd_cf_entry :
  snd (frd_RUN frd_ss0) = PTS_stopped (SR_branch BC_EQ SV_rpos SV_rend)
  /\ ss_pc (frd_stop frd_ss0) = 108.
Proof. vm_compute. split; reflexivity. Qed.

(* the window is empty: 0x8ef90 `bnez s6`, the zero-size test *)
Definition frd_ssA : sstate := frd_stop (frd_with BC_EQ SV_rpos SV_rend (frd_stop frd_ss0)).
Lemma frd_cf_A :
  snd (frd_RUN (frd_with BC_EQ SV_rpos SV_rend (frd_stop frd_ss0)))
    = PTS_stopped (SR_branch BC_NE SV_total (SLit 0))
  /\ ss_pc frd_ssA = 308.
Proof. vm_compute. split; reflexivity. Qed.

(* nm = 0: no call at all. The walk runs to the return at 0x8ef88 with a0 = nmemb, the FILE's
   rpos and rend untouched, and only the orientation word written. *)
Lemma frd_cf_A_zero :
  snd (frd_RUN (frd_with BC_EQ SV_total (SLit 0) frd_ssA)) = PTS_stopped (SR_jalr (SOff 1 0))
  /\ ss_pc (frd_stop (frd_with BC_EQ SV_total (SLit 0) frd_ssA)) = 300
  /\ sr_get (ss_regs (frd_stop (frd_with BC_EQ SV_total (SLit 0) frd_ssA))) 10%bv = SOff 12 0
  /\ sr_get (ss_regs (frd_stop (frd_with BC_EQ SV_total (SLit 0) frd_ssA))) 1%bv = SOff 1 0
  /\ sr_get (ss_regs (frd_stop (frd_with BC_EQ SV_total (SLit 0) frd_ssA))) 2%bv = SOff 2 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* nm > 0 with an empty window: the first call is __toread, and the walk resumes at 0x8ef04. *)
Lemma frd_cf_A_call :
  snd (frd_RUN (frd_with BC_NE SV_total (SLit 0) frd_ssA)) = PTS_call FS_toread
  /\ ss_pc (frd_stop (frd_with BC_NE SV_total (SLit 0) frd_ssA)) = 168.
Proof. vm_compute. split; reflexivity. Qed.

(* the window is not empty: 0x8eed0 `bltu s4, s6`, which caps the copy at the window *)
Definition frd_ssB : sstate := frd_stop (frd_with BC_NE SV_rpos SV_rend (frd_stop frd_ss0)).
Lemma frd_cf_B :
  snd (frd_RUN (frd_with BC_NE SV_rpos SV_rend (frd_stop frd_ss0)))
    = PTS_stopped (SR_branch BC_LTU SV_win SV_total)
  /\ ss_pc frd_ssB = 116.
Proof. vm_compute. split; reflexivity. Qed.

(* either arm of that test calls the memory-copy trampoline and resumes at 0x8eee4 *)
Lemma frd_cf_B_call_short :
  snd (frd_RUN (frd_with BC_LTU SV_win SV_total frd_ssB)) = PTS_call FS_memcpy
  /\ ss_pc (frd_stop (frd_with BC_LTU SV_win SV_total frd_ssB)) = 136.
Proof. vm_compute. split; reflexivity. Qed.
Lemma frd_cf_B_call_full :
  snd (frd_RUN (frd_with BC_GEU SV_win SV_total frd_ssB)) = PTS_call FS_memcpy
  /\ ss_pc (frd_stop (frd_with BC_GEU SV_win SV_total frd_ssB)) = 136.
Proof. vm_compute. split; reflexivity. Qed.

Lemma fr_apresent_grows : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a G [Hh [bb Hb]]. split; [exact Hh|].
specialize (G (Z_to_bv 64 a)). unfold mrestrict in G. rewrite Hh, Hb in G.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity | exfalso; apply G; congruence].
Qed.
Lemma fr_val_mem_aview_eq : forall H (m m' : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v ->
  forall x, a <= x < a + Z.of_nat n -> aview segs H m' x = aview segs H m x.
Proof.
intros H m m' a n v V1 V2 x Hx. unfold aview.
assert (Hk : (Z.to_nat (x - a) < n)%nat) by lia.
pose proof (V1 _ Hk) as E1. pose proof (V2 _ Hk) as E2.
replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E1, E2 by lia. rewrite E1, E2. reflexivity.
Qed.
Lemma frd_chunk_val4 : forall E m base off e,
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 4 e)) ->
  (forall i, 0 <= i < 4 -> YP09.byte_of_word (sv_denot E e) i = Z_to_bv 8 (le_byte U32M1 4 (Z.to_nat i))) ->
  val_mem segs m (base + off) 4 U32M1.
Proof.
intros E m base off e Hc Hb k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b0 & Hcb & Hmb).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hcb. injection Hcb as <-.
cbn [YP09.c_off] in Hmb. rewrite Hmb. f_equal.
rewrite (Hb (Z.of_nat k) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
Qed.

Definition RUNF := fr_run segs B LAWS segs_low Hwx tbl tbl_ok val sigma frd_listing Hcert HBok frd_lim frd_len.
Definition RETF := fr_ret_at segs Hwx tbl tbl_ok val sigma frd_listing Hcert.

(* ---------------------------------------------------------------------- *)
(* The B-full leaf (the window covers the request): the arithmetic of the  *)
(* two branch tests, the region_kept clause of a memory-copy call, and the *)
(* list facts of the copied prefix and the drained window.                 *)
(* ---------------------------------------------------------------------- *)
Lemma frd_U_total : forall E nm,
  ew E 12 = w64 nm -> ew E 11 = w64 1 -> 0 <= nm < 2 ^ 64 ->
  U E (SMd M_MUL (SOff 12 0) (SOff 11 0)) = nm.
Proof.
intros E nm H12 H11 Hnm. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E 12 nm H12 Hnm), (U_atom E 11 1 H11 ltac:(lia)).
rewrite Z.mul_1_r. apply zcanon_id. unfold M64. lia.
Qed.
Lemma frd_U_win : forall E rp re L,
  ew E 32 = w64 rp -> ew E 33 = w64 re ->
  0 <= rp < 2 ^ 64 -> 0 <= re < 2 ^ 64 -> re = rp + L -> 0 <= L ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0)) = L.
Proof.
intros E rp re L H32 H33 Hrp Hre Hrr HL.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E 32 rp H32 Hrp), (U_atom E 33 re H33 Hre), U_SLit.
unfold zcanon, M64. rewrite Zplus_mod_idemp_l.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
replace (rp * (2 ^ 64 - 1) + re) with ((re - rp) + rp * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite Hrr.
replace (rp + L - rp) with L by lia. apply Z.mod_small. lia.
Qed.
Lemma frd_U_s4 : forall E nm,
  ew E 12 = w64 nm -> ew E 11 = w64 1 -> 0 <= nm < 2 ^ 64 ->
  U E (SAlu ALU_SUB (SMd M_MUL (SOff 12 0) (SOff 11 0))
                    (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SOff 11 0)) (SLit 0))) = 0.
Proof.
intros E nm H12 H11 Hnm. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (frd_U_total E nm H12 H11 Hnm), U_SLit.
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r.
rewrite (zcanon_id nm) by (unfold M64; lia). rewrite Z.sub_diag.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma frd_base_even : forall z, z mod 4 = 0 -> (z + 136) mod 2 = 0.
Proof.
intros z H. pose proof (Z_div_mod_eq_full z 4) as HD. rewrite H, Z.add_0_r in HD.
rewrite HD. replace (4 * (z / 4) + 136) with ((2 * (z / 4) + 68) * 2) by lia. apply Z_mod_mult.
Qed.
Lemma frd_env_agree_havoc : forall vl regs extra ws,
  env_agree 32 (Ereg regs extra) (havoc (Eimg vl (Ereg regs extra)) 36%nat ws).
Proof.
intros vl regs extra ws. split.
- intros n Hn. rewrite ew_havoc_old by lia. apply Eimg_low. unfold A_TEXT. lia.
- reflexivity.
Qed.
Lemma frd_mbyte_of_aview2 : forall H H' (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a') as [b'|], (mbyte segs (mrestrict H m) a) as [bb|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma frd_denot_nm2 : forall E nm,
  ew E 12 = w64 nm -> ew E 11 = w64 1 -> 0 <= nm < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SOff 11 0)) (SLit 0)) (SLit 0))
    = w64 nm.
Proof.
intros E nm H12 H11 Hnm. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (frd_U_total E nm H12 H11 Hnm), U_SLit.
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite !Z.add_0_r.
rewrite (zcanon_id nm) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
Qed.
Lemma frd_denot_rp_nm : forall E rp nm,
  ew E 32 = w64 rp -> ew E 12 = w64 nm -> ew E 11 = w64 1 ->
  0 <= rp -> 0 <= nm -> rp + nm < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 32 0)
                (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SOff 11 0)) (SLit 0))) = w64 (rp + nm).
Proof.
intros E rp nm H32 H12 H11 Hrp Hnm Hsum. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 32 rp H32 ltac:(lia)), (frd_U_total E nm H12 H11 ltac:(lia)), U_SLit.
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r.
rewrite (zcanon_id nm) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
Qed.
Lemma frd_writable_kept : forall (H : word -> bool) (m m2 : word -> option byte) a,
  (apresent H m a -> apresent H m2 a) ->
  writable_at segs (mrestrict H m) a -> writable_at segs (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [bb|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ bb Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma frd_region_kept_av : forall E (H : word -> bool) (m m2 : word -> option byte) n bb lo hi wlo whi cs,
  bv_unsigned (ew E n) = bb ->
  (forall a, bb + lo <= a < bb + hi -> aview segs H m2 a = aview segs H m a) ->
  (forall a, apresent H m a -> apresent H m2 a) ->
  region_kept segs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n bb lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- exact (frd_writable_kept H m m2 a (Hp a)).
Qed.
Lemma frd_firstn_window : forall (C Wl : list Z) p cpos j,
  Wl = firstn (Z.to_nat (cpos - p)) (skipn (Z.to_nat p) C) -> 0 <= j <= Z.of_nat (length Wl) ->
  firstn (Z.to_nat j) (skipn (Z.to_nat p) C) = firstn (Z.to_nat j) Wl.
Proof.
intros C Wl p cpos j HW Hj. subst Wl. rewrite firstn_firstn.
rewrite length_firstn, length_skipn in Hj. f_equal. lia.
Qed.
Lemma frd_garr8_skipn : forall (m : word -> option byte) base (l : list Z) (j : nat),
  (j <= length l)%nat -> garr8 segs m base l -> garr8 segs m (base + Z.of_nat j) (skipn j l).
Proof.
intros m base l j Hj H. rewrite <- (firstn_skipn j l) in H.
apply (proj1 (garr8_app segs m base (firstn j l) (skipn j l))) in H.
destruct H as [_ H2]. rewrite length_firstn in H2. rewrite Nat.min_l in H2 by exact Hj. exact H2.
Qed.
Lemma frd_garr8_copy : forall (m m' : word -> option byte) src dst (l : list Z) (j : nat),
  garr8 segs m src l -> (j <= length l)%nat ->
  (forall i, 0 <= i < Z.of_nat j -> mbyte segs m' (dst + i) = mbyte segs m (src + i)) ->
  garr8 segs m' dst (firstn j l).
Proof.
intros m m' src dst l j H Hj Hag i Hi.
rewrite length_firstn in Hi. rewrite Nat.min_l in Hi by exact Hj.
assert (Hn : nth i (firstn j l) 0 = nth i l 0).
{ rewrite <- (firstn_skipn j l) at 2. rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity. }
rewrite Hn. destruct (H i ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. assert (Hk0 : kk = 0%nat) by lia. subst kk.
cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite (Hag (Z.of_nat i) ltac:(lia)). exact Hv.
Qed.
Ltac frd_reg_call HS r Hr :=
lazymatch type of HS with
| st_ok ?segsx ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segsx H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

(* Read a register off a call-state st_ok hypothesis (the pi-free analogue of frd_reg). *)
Ltac lreg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?sg ?Ev ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H Ev ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr
  end.

(* A region whose extent a call left as it was and whose write window is present afterwards
   is region_kept across the call (the reseat's fr_after_call premise). *)
Lemma frd_region_kept : forall E (W W2 : world segs) (memc mem2 : word -> option byte) (n : nat) bs lo hi wlo whi cs,
  bv_unsigned (ew E n) = bs ->
  (forall a, bs + lo <= a < bs + hi -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, bs + wlo <= a < bs + whi -> apresent (w_H W2) mem2 a) ->
  region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E W W2 memc mem2 n bs lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.
Lemma frd_ew_havoc : forall E k ws (n : nat) v, (n < k)%nat -> ew E n = v -> ew (havoc E k ws) n = v.
Proof. intros E k ws n v Hn H. rewrite ew_havoc_old by exact Hn. exact H. Qed.
Lemma frd_base_havoc : forall E k ws (n : nat) v, (n < k)%nat -> base_val E (Some n) = v ->
  base_val (havoc E k ws) (Some n) = v.
Proof. intros E k ws n v Hn H. cbn [base_val] in *. rewrite ew_havoc_old by exact Hn. exact H. Qed.
Lemma frd_ea_havoc : forall vl regs extra k ws, (32 <= k)%nat ->
  env_agree 32 (Ereg regs extra) (havoc (Eimg vl (Ereg regs extra)) k ws).
Proof.
intros vl regs extra k ws Hk. split; [|reflexivity].
intros n Hn. rewrite ew_havoc_old by lia. apply Eimg_low. unfold A_TEXT. lia.
Qed.
Lemma frd_ea_havoc2 : forall E0 E k ws, env_agree 32 E0 E -> (32 <= k)%nat -> env_agree 32 E0 (havoc E k ws).
Proof.
intros E0 E k ws [H1 H2] Hk. split; [|exact H2].
intros n Hn. rewrite ew_havoc_old by lia. apply H1. exact Hn.
Qed.
(* fread's size * nmemb with size = 1, and the return value (s6 - s4) / s1 = 0 of the paths that
   return before any byte is delivered (0x8ef5c-0x8ef60). *)
Lemma frd_U_mul : forall E nm, ew E 12 = w64 nm -> ew E 11 = w64 1 -> 0 <= nm <= 2 ^ 26 ->
  U E (SMd M_MUL (SOff 12 0) (SOff 11 0)) = nm.
Proof.
intros E nm H12 H11 Hr. rewrite U_SMd, !U_SOff, H12, H11. unfold w64.
rewrite !unsigned_lit_small by lia. cbn [zmd_raw]. rewrite !Z.add_0_r.
rewrite (zcanon_id 1) by (unfold M64; lia). rewrite (zcanon_id nm) by (unfold M64; lia).
rewrite Z.mul_1_r. apply zcanon_id. unfold M64; lia.
Qed.
Lemma frd_U_ret0 : forall E nm, ew E 12 = w64 nm -> ew E 11 = w64 1 -> 0 <= nm <= 2 ^ 26 ->
  U E (SMd M_DIVU (SAlu ALU_SUB (SMd M_MUL (SOff 12 0) (SOff 11 0))
                     (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SOff 11 0)) (SLit 0))) (SOff 11 0)) = 0.
Proof.
intros E nm H12 H11 Hr. pose proof (frd_U_mul E nm H12 H11 Hr) as Hm.
assert (H1 : U E (SOff 11 0) = 1).
{ rewrite U_SOff, H11. unfold w64. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64; lia. }
rewrite U_SMd, U_SAlu, U_SAlu, Hm, U_SLit, H1. cbn [zmd_raw zalu_raw].
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r. rewrite (zcanon_id nm) by (unfold M64; lia).
rewrite Z.sub_diag. reflexivity.
Qed.
(* the length mread gets: a2 = s4 + 0 = size * nmemb with size = 1 (0x8ef14 mv a2, s4) *)
Lemma frd_U_a2 : forall E nm, ew E 12 = w64 nm -> ew E 11 = w64 1 -> 0 <= nm <= 2 ^ 26 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SOff 11 0)) (SLit 0)) (SLit 0)) = nm.
Proof.
intros E nm H12 H11 Hr. pose proof (frd_U_mul E nm H12 H11 Hr) as Hm.
rewrite U_SAlu, U_SAlu, Hm, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite !Z.add_0_r.
rewrite !(zcanon_id nm) by (unfold M64; lia). reflexivity.
Qed.
(* 0x8ef18: jalr ra, 0(a3) *)
Lemma frd_D_jalr : decode_any (Z_to_bv 32 0x680e7) = Some (Jalr (1%bv : bv 5) (13%bv : bv 5) (0%bv : bv 12), 4%Z).
Proof.
lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end.
Qed.
(* s4 after mread returned k (0x8ef20 sub s4, s4, a0): nm - k *)
Lemma frd_U_s4k : forall E nm j, ew E 12 = w64 nm -> ew E 11 = w64 1 -> ew E 68 = w64 j ->
  0 <= nm <= 2 ^ 26 -> 0 <= j <= nm ->
  U E (SAlu ALU_SUB (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SOff 11 0)) (SLit 0)) (SOff 68 0)) = nm - j.
Proof.
intros E nm j H12 H11 H68 Hr Hj. pose proof (frd_U_mul E nm H12 H11 Hr) as Hm.
assert (Hj' : U E (SOff 68 0) = j).
{ rewrite U_SOff, H68. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64; lia. }
rewrite U_SAlu, U_SAlu, Hm, U_SLit, Hj'. cbn [zalu_raw].
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r. rewrite (zcanon_id nm) by (unfold M64; lia).
apply zcanon_id. unfold M64; lia.
Qed.
(* the return value (s6 - s4) / s1 after mread delivered k < nm bytes (0x8ef5c-0x8ef60): k *)
Lemma frd_U_retk : forall E nm j, ew E 12 = w64 nm -> ew E 11 = w64 1 -> ew E 68 = w64 j ->
  0 <= nm <= 2 ^ 26 -> 0 <= j <= nm ->
  U E (SMd M_DIVU (SAlu ALU_SUB (SMd M_MUL (SOff 12 0) (SOff 11 0))
                     (SAlu ALU_SUB (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SOff 11 0)) (SLit 0)) (SOff 68 0)))
                   (SOff 11 0)) = j.
Proof.
intros E nm j H12 H11 H68 Hr Hj.
pose proof (frd_U_mul E nm H12 H11 Hr) as Hm.
pose proof (frd_U_s4k E nm j H12 H11 H68 Hr Hj) as Hs.
assert (H1 : U E (SOff 11 0) = 1).
{ rewrite U_SOff, H11. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64; lia. }
rewrite U_SMd, U_SAlu, Hs, Hm, H1. cbn [zalu_raw zmd_raw Z.eqb].
replace (nm - (nm - j)) with j by ring.
rewrite Z.div_1_r. rewrite !(zcanon_id j) by (unfold M64; lia). reflexivity.
Qed.
(* The destination bytes a call kept: d .. d+l lies in a side-stack frame, on the stack or in a
   live block (rread_at), outside the call's window and its write set. *)
Lemma frd_dest_kept : forall R lyc Sc (W : world segs) memc (W2 : world segs) mem2 sp E d l,
  rread_kept segs B R lyc Sc W memc W2 mem2 sp E ->
  rread_at B lyc Sc d l ->
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 64 ->
  (forall a, d <= a < d + l -> ~ E a /\ ~ (sp - R <= a < sp)) ->
  forall a, d <= a < d + l -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a.
Proof.
intros R lyc Sc W memc W2 mem2 sp E d l (K1 & K2 & K3 & K4 & K5 & K6) Hat Hc Hh Hd a Ha.
destruct (Hd a Ha) as (HnE & Hnw).
destruct Hat as [(cid & pos & Hin & Hr) | [(Hlo & Hhi) | (bb & nn & Hin & H1 & H2)]].
- apply (K4 cid pos a Hin); [left; exact (Hr a Ha) | exact HnE].
- apply K1; [lia | exact Hnw | exact HnE].
- pose proof (req_size_pos nn ltac:(lia)) as Hrq.
  replace a with (bb + (a - bb)) by lia. apply (K2 bb nn (a - bb) Hin); [lia|].
  replace (bb + (a - bb)) with a by lia. exact HnE.
Qed.
(* What a last run kept (global agreement outside fread's frame), composed onto what the path
   kept before it. *)
Lemma frd_kept_extend : forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 md2 memF sp E,
  rread_kept segs B RFREAD_STK lyc Sc W memc W2 mem2 sp E ->
  AR segs B lyc Sc W2 mem2 md2 ->
  alloc_ceiling <= sp - RFREAD_STK -> sp <= 2 ^ 64 ->
  (forall a, sp - RFREAD_STK <= a < sp -> apresent (w_H W) memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - RFREAD_STK <= a < sp) ->
     aview segs (w_H W2) memF a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memF a) ->
  (forall a, sp - RFREAD_STK <= a < sp -> apresent (w_H W2) memF a) ->
  rread_kept segs B RFREAD_STK lyc Sc W memc W2 memF sp E.
Proof.
intros lyc Sc W memc W2 mem2 md2 memF sp E HK HAR2 Hc Hsp Hp0 Hag Hgrow Hwin.
assert (HK3 : rread_kept segs B RFREAD_STK lyc Sc W2 mem2 W2 memF sp E).
{ apply (frd_kept_of_agree_all segs B LAWS RFREAD_STK lyc Sc W2 mem2 md2 W2 memF sp E HAR2 Hc).
  - intros a Ha Hs _. exact (Hag a Ha Hs).
  - intros a Hi. pose proof (segs_low a Hi) as Hl. apply Hag; [unfold kLowMemEnd in Hl; lia|].
    pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac. unfold kLowMemEnd in *. lia.
  - exact Hgrow.
  - exact Hwin. }
exact (frd_kept_trans segs B RFREAD_STK RFREAD_STK RFREAD_STK lyc Sc W memc W2 mem2 W2 memF sp sp sp E E E HK HK3
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc Hsp Hp0 (fun a h => h) (fun a h => h)).
Qed.

(* ===== B-short leaf helper lemmas (a Theorem Labs lane) ===== *)
(* the a2 value at the memcpy call: rend + rpos*(2^64-1) = |Wl| (rend - rpos), where the
   symbolic engine writes the -1 immediate as its unsigned image 2^64-1. *)
Lemma frd_win_val : forall rp re L, 0 <= rp -> rp <= re -> re < 2 ^ 64 -> L mod 2 ^ 64 = 2 ^ 64 - 1 ->
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 rp) (Z_to_bv 64 L)) (Z_to_bv 64 re)
  = Z_to_bv 64 (re - rp).
Proof.
intros rp re L Hrp Hle Hre HL.
rewrite m_mul, alu_add. unfold v_mul, v_add.
apply Z_to_bv64_eq_mod.
rewrite (unsigned_lit_small rp) by lia.
rewrite (unsigned_lit_small re) by lia.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, HL, Zplus_mod_idemp_l.
replace (rp * (2 ^ 64 - 1) + re) with ((re - rp) + rp * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. reflexivity.
Qed.
(* the rpos the walk stores after the window copy, rp*2^64 + re (the engine's image of rp + |Wl|),
   denotes re. *)
Lemma frd_rpos_val : forall rp re, 0 <= re < 2 ^ 64 ->
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 rp) (Z_to_bv 64 18446744073709551616)) (Z_to_bv 64 re)
  = Z_to_bv 64 re.
Proof.
intros rp re Hre.
assert (H0 : Z_to_bv 64 18446744073709551616 = Z_to_bv 64 0) by (apply Z_to_bv64_eq_mod; vm_compute; reflexivity).
rewrite H0, m_mul, alu_add. unfold v_mul, v_add.
rewrite (unsigned_lit_small 0) by lia. rewrite Z.mul_0_r.
rewrite (unsigned_lit_small 0) by lia. rewrite Z.add_0_l.
rewrite (unsigned_lit_small re) by lia. reflexivity.
Qed.
(* s3 after the window copy (0x8eeec add s3, s3, s4): d + rp*(2^64-1) + re denotes d + |Wl|. *)
Lemma frd_bs_a1_val : forall dd rp re L, 0 <= dd < 2 ^ 64 -> 0 <= rp -> rp <= re -> re < 2 ^ 64 ->
  L mod 2 ^ 64 = 2 ^ 64 - 1 -> dd + (re - rp) < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_ADD (Z_to_bv 64 dd) (mul_div M_MUL (Z_to_bv 64 rp) (Z_to_bv 64 L))) (Z_to_bv 64 re)
  = Z_to_bv 64 (dd + (re - rp)).
Proof.
intros dd rp re L Hd Hrp Hle Hre HL Hs.
rewrite m_mul, alu_add. unfold v_mul, v_add.
apply Z_to_bv64_eq_mod.
rewrite alu_add. unfold v_add.
rewrite (unsigned_lit_small dd) by lia. rewrite (unsigned_lit_small rp) by lia. rewrite (unsigned_lit_small re) by lia.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, HL.
rewrite Zplus_mod_idemp_l.
replace (dd + (rp * (2 ^ 64 - 1)) mod 2 ^ 64 + re) with ((rp * (2 ^ 64 - 1)) mod 2 ^ 64 + (dd + re)) by ring.
rewrite Zplus_mod_idemp_l.
replace (rp * (2 ^ 64 - 1) + (dd + re)) with ((dd + (re - rp)) + rp * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. reflexivity.
Qed.
(* s4 = nm - |Wl| (0x8eef4 sub s4, s6, s4) *)
Lemma frd_bs_s4_val : forall nm rp re, 0 <= rp -> rp <= re -> re < 2 ^ 64 -> re - rp <= nm -> nm < 2 ^ 64 ->
  alu64 ALU_SUB (mul_div M_MUL (Z_to_bv 64 nm) (Z_to_bv 64 1))
    (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 rp) (Z_to_bv 64 (-1))) (Z_to_bv 64 re))
  = Z_to_bv 64 (nm - (re - rp)).
Proof.
intros nm rp re Hrp Hle Hre Hn Hnm.
rewrite (frd_win_val rp re (-1)) by first [lia | (vm_compute; reflexivity)].
rewrite m_mul, (v_mul_one nm) by lia.
rewrite alu_sub. unfold v_sub. rewrite (unsigned_lit_small nm) by lia. rewrite (unsigned_lit_small (re - rp)) by lia.
reflexivity.
Qed.
(* a2 = s4 + 0 (0x8ef14 mv a2, s4) *)
Lemma frd_bs_a2_val : forall nm rp re, 0 <= rp -> rp <= re -> re < 2 ^ 64 -> re - rp <= nm -> nm < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_SUB (mul_div M_MUL (Z_to_bv 64 nm) (Z_to_bv 64 1))
    (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 rp) (Z_to_bv 64 (-1))) (Z_to_bv 64 re))) (Z_to_bv 64 0)
  = Z_to_bv 64 (nm - (re - rp)).
Proof.
intros nm rp re Hrp Hle Hre Hn Hnm.
rewrite (frd_bs_s4_val nm rp re) by lia.
rewrite alu_add. unfold v_add. rewrite (unsigned_lit_small (nm - (re - rp))) by lia.
rewrite (unsigned_lit_small 0) by lia. rewrite Z.add_0_r. reflexivity.
Qed.

(* register value from a raw st_ok at a call/stop state, as the dev's frd_reg does for st_ok_pi. *)
Ltac frd_reg0 HS r Hr :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg sg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* assembling the delivered bytes: the window part then the mread part. *)
Lemma frd_firstn_add : forall {A} (a b : nat) (l : list A),
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
induction a as [|a IH]; intros b l; [reflexivity|].
destruct l as [|x l]; simpl; [rewrite firstn_nil; reflexivity | rewrite IH; reflexivity].
Qed.
Lemma frd_firstn_skipn_app : forall (C : list Z) (p a b : nat),
  firstn (a + b) (skipn p C) = firstn a (skipn p C) ++ firstn b (skipn (p + a) C).
Proof.
intros C p a b. rewrite frd_firstn_add. rewrite skipn_skipn.
replace (a + p)%nat with (p + a)%nat by lia. reflexivity.
Qed.
(* the B-short walk's s4 after the window copy, after mread's k, and the return (s6 - s4) / s1 *)
Lemma frd_bs_U_s4 : forall E nm rp re,
  ew E 12 = w64 nm -> ew E 11 = w64 1 -> ew E 32 = w64 rp -> ew E 33 = w64 re ->
  0 <= rp -> rp <= re -> re < 2 ^ 64 -> re - rp <= nm -> nm < 2 ^ 64 ->
  U E (SAlu ALU_SUB (SMd M_MUL (SOff 12 0) (SOff 11 0))
         (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0))) = nm - (re - rp).
Proof.
intros E nm rp re H12 H11 H32 H33 Hrp Hle Hre Hn Hnm.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (frd_U_total E nm H12 H11 ltac:(lia)).
rewrite (frd_U_win E rp re (re - rp) H32 H33 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma frd_bs_U_s4k : forall E nm rp re j (n : nat),
  ew E 12 = w64 nm -> ew E 11 = w64 1 -> ew E 32 = w64 rp -> ew E 33 = w64 re -> ew E n = w64 j ->
  0 <= rp -> rp <= re -> re < 2 ^ 64 -> re - rp <= nm -> nm < 2 ^ 64 -> 0 <= j <= nm - (re - rp) ->
  U E (SAlu ALU_SUB (SAlu ALU_SUB (SMd M_MUL (SOff 12 0) (SOff 11 0))
         (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0))) (SOff n 0)) = nm - (re - rp) - j.
Proof.
intros E nm rp re j n H12 H11 H32 H33 Hn' Hrp Hle Hre Hn Hnm Hj.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (frd_bs_U_s4 E nm rp re H12 H11 H32 H33 Hrp Hle Hre Hn Hnm), (U_atom E n j Hn' ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma frd_bs_divu1 : forall x, zmd_raw 64 M_DIVU x 1 = x.
Proof. intros x. unfold zmd_raw. cbv beta iota zeta. change (1 =? 0) with false. cbv iota. apply Z.div_1_r. Qed.
Lemma frd_bs_U_ret : forall E nm s4v e4,
  ew E 12 = w64 nm -> ew E 11 = w64 1 -> 0 <= nm < 2 ^ 64 -> U E e4 = s4v -> 0 <= s4v <= nm ->
  U E (SMd M_DIVU (SAlu ALU_SUB (SMd M_MUL (SOff 12 0) (SOff 11 0)) e4) (SOff 11 0)) = nm - s4v.
Proof.
intros E nm s4v e4 H12 H11 Hnm He4 Hs.
rewrite U_SMd, U_SAlu, He4, (frd_U_total E nm H12 H11 Hnm), (U_atom E 11 1 H11 ltac:(lia)).
cbn [zalu_raw]. rewrite (zcanon_id (nm - s4v)) by (unfold M64; lia).
rewrite frd_bs_divu1. apply zcanon_id. unfold M64. lia.
Qed.
(* a sub-range of where the destination lies lies there too *)
Lemma frd_rread_at_sub : forall lyc Sc d l d' l', rread_at B lyc Sc d l ->
  d <= d' -> d' + l' <= d + l -> 0 <= l' -> rread_at B lyc Sc d' l'.
Proof.
intros lyc Sc d l d' l' Hat H1 H2 H3.
destruct Hat as [(cid & pos & Hin & Hr) | [(Hlo & Hhi) | (bb & nn & Hin & Hb1 & Hb2)]].
- left. exists cid, pos. split; [exact Hin|]. intros a Ha. apply Hr. lia.
- right. left. split; lia.
- right. right. exists bb, nn. split; [exact Hin|]. split; lia.
Qed.

Theorem frd_walk : rfread_contract segs B K (val A_TEXT).
Proof.
unfold rfread_contract.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch d nm f b p C HPRE.
destruct HPRE as (HCALL & G10 & G11 & G12 & G13 & Hblkf & Hblkb & Hbstk & HSRC & HWRF & Hnm & HDEST).
destruct HDEST as (Hdf & Hdb & Hd0 & Hdam & Hdat & Hdwr & Hdra & Hdhull).
destruct HCALL as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hstk1 & Hsple & Hchain).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & Hgone & Hpres0 & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal0 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK HAR Hblkf)
  as (Hf16 & Hf0 & Hfceil & Hfapp & Hfbytes & Hfdisj & Hfrange).
assert (RQ : req_size SRC_FILE_BLOCK = SRC_FILE_BLOCK) by reflexivity. rewrite RQ in *.
pose proof HSRC as HSRC0.
destruct HSRC as (Wl & cpos & fl & mdv & Hp0 & Hpc & Hcn & Hnlt & Hbw & Hcpos & HWl & Hbok & Hgarr &
  HST & HWIN & HFL & HEOF & HMD & HCK & HENV & HOFL & Hfnz).
assert (Hsp44 : 2 ^ 44 <= spZ regs) by (unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia).
assert (Hsp47 : spZ regs <= 2 ^ 47) by lia.
assert (Hfstk : f + SRC_FILE_BLOCK <= spZ regs - 64)
  by (change SRC_FILE_BLOCK with 1304 in *; unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia).
assert (Hpres : forall a, spZ regs - 64 <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia).
(* the window cells, in one package covering both arms of source_window *)
assert (HW : exists rp re,
  val_mem segs (rd W memc) (f + 8) 8 rp /\ val_mem segs (rd W memc) (f + 16) 8 re /\
  0 <= rp /\ re <= f + SRC_FILE_BLOCK /\ re = rp + Z.of_nat (length Wl) /\
  (Wl <> [] -> f + SRC_BUF_OFF <= rp /\ garr8 segs (rd W memc) rp Wl)).
{ destruct HWIN as [(-> & H8 & H16) | (i & Hi0 & Hi1 & H8 & H16 & Hg)].
  - exists 0, 0. cbn [length]. split; [exact H8|]. split; [exact H16|].
    split; [lia|]. split; [change SRC_FILE_BLOCK with 1304 in *; lia|]. split; [reflexivity|].
    intros Hne. exfalso. apply Hne. reflexivity.
  - exists (f + SRC_BUF_OFF + i), (f + SRC_BUF_OFF + i + Z.of_nat (length Wl)).
    split; [exact H8|]. split; [exact H16|].
    split; [change SRC_BUF_OFF with 280 in *; lia|].
    split; [change SRC_BUF_OFF with 280 in *; change SRC_BUFSIZ with 1024 in *; change SRC_FILE_BLOCK with 1304 in *; lia|].
    split; [lia|]. intros _. split; [lia | exact Hg]. }
destruct HW as (rp & re & M8 & M16 & Hrp0 & Hrehi & Hrere & Hgw).
pose proof HST as (Hfdr & Hread & Hwrite & Hseek & Hbufb & Hbufs & Hck1 & Hck2 & Hck3 & Hck4 &
  Hcptr & Hz32 & Hz40 & Hz48 & Hz56 & Hprev & Hnext & Hgetln & Hfd120 & Hlock & Hlbf &
  Hfpos & Hfal & Hbpos & Hdisjfb).
pose proof HMD as (Hmdv & Hmdcase).
assert (HS0 : st_ok_pi segs val (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) frd_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0)) memc (seg_rom segs)))).
{ apply (frd_entry W lyc Sc regs memc mdc d nm f rp re mdv); try assumption;
  try (change SRC_FILE_BLOCK with 1304 in *; unfold U32M1 in *; lia).
  all: try (change SRC_FILE_BLOCK with 1304 in *; unfold U32M1 in *; lia).
  all: try (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hdam; lia).
  all: try (destruct Hmread_pc; lia). }
rewrite Z.add_0_r in HS0.
assert (HE11 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 11 = w64 1).
{ rewrite (Eimg_low val _ 11%nat ltac:(cbv [A_TEXT]; lia)). rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl). exact G11. }
assert (HE12 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 12 = w64 nm).
{ rewrite (Eimg_low val _ 12%nat ltac:(cbv [A_TEXT]; lia)). rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl). exact G12. }
assert (HE32 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 32 = w64 rp).
{ rewrite (Eimg_low val _ 32%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_extra regs _ 0). }
assert (HE33 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 33 = w64 re).
{ rewrite (Eimg_low val _ 33%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_extra regs _ 1). }
assert (HE35 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 35 = w64 mdv).
{ rewrite (Eimg_low val _ 35%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_extra regs _ 3). }
assert (Hrere64 : re <= f + SRC_FILE_BLOCK < 2 ^ 64) by (change SRC_FILE_BLOCK with 1304 in *; lia).
assert (VB2 : base_val (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) (Some 2%nat) = spZ regs)
  by (rewrite (fr_base_reg val regs _ 2%nat 2%bv eq_refl ltac:(cbv [A_TEXT]; lia)); reflexivity).
assert (VB13 : base_val (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) (Some 13%nat) = f)
  by (rewrite (fr_base_reg val regs _ 13%nat 13%bv eq_refl ltac:(cbv [A_TEXT]; lia)), G13;
      unfold w64; apply unsigned_lit_small; change SRC_FILE_BLOCK with 1304 in *; lia).
assert (AWRgen : forall a, (spZ regs - 64 <= a < spZ regs) \/ (f + 8 <= a < f + 16) \/ (f + 136 <= a < f + 140) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ intros a [Ha | [Ha | Ha]].
  - left. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
  - apply (proj1 (HWRF a ltac:(change SRC_FILE_BLOCK with 1304 in *; lia))).
  - apply (proj1 (HWRF a ltac:(change SRC_FILE_BLOCK with 1304 in *; lia))). }
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) (mrestrict (w_H W) memc))
  by apply Forall_nil.
assert (HEI0 : PaRun.img_env val A_LIMF (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]))
  by (apply Eimg_env; exact Hvalrange).
unfold cfg_at, w64 at 1.
frd_run RUNF HS0 HJ SHOK.
{ intros a (r0 & Hin & Hr0). cbn [ss_mem frd_ss0 In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
  unfold frd_stkR, frd_fileR1, frd_fileR2 in Hr0;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0; rewrite ?VB2, ?VB13 in Hr0;
  apply AWRgen; lia. }
frd_branch_auto; clear HS0; intros Hc HS0.
- (* A: the window is empty (rpos = rend), so |Wl| = 0 *)
  frd_run RUNF HS0 HJ SHOK.
  { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
    rewrite ?VB2, ?VB13 in Hr0; apply AWRgen; lia. }
  frd_branch_auto; clear HS0; intros Hc2 HS0.
  + (* nm <> 0: the __toread call *)
    frd_run RUNF HS0 HJ SHOK.
    { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
      rewrite ?VB2, ?VB13 in Hr0; apply AWRgen; lia. }
    (* the stream, transported to the __toread call state: only the orientation word +136 and
       the stack frame changed from the entry memory. *)
    set (ZS := fun a => (spZ regs - 64 <= a < spZ regs) \/ (f + 8 <= a < f + 16) \/ (f + 136 <= a < f + 140)).
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr
      ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZS; lia|]);
            destruct Hin)) as U0.
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr0
      ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZS; lia|]);
            destruct Hin)) as U1.
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr1
      ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZS; lia|]);
            destruct Hin)) as U2.
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ZS a -> aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Ha Hz. rewrite (U2 a Ha Hz), (U1 a Ha Hz), (U0 a Ha Hz). reflexivity. }
    clear U0 U1 U2.
    lazymatch type of HS0 with st_ok _ ?Ev ?ss ?msr =>
      pose proof (st_ok_mem_ok segs Ev ss msr HS0) as (_ & HRS & _) end.
    cbn [ss_mem restrict mkst ms_mem] in HRS.
    pose proof (Forall_inv (Forall_inv_tail HRS)) as HR1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HRS))) as HR2.
    destruct HR1 as (_ & _ & _ & HC1). destruct HR2 as (_ & _ & _ & HC2c).
    cbn [YP09.r_base YP09.r_chunks] in HC1, HC2c. rewrite VB13 in HC1, HC2c.
    pose proof (Forall_inv HC1) as CK8.
    pose proof (Forall_inv (Forall_inv_tail HC1)) as CK16.
    pose proof (Forall_inv HC2c) as CK136.
    assert (N8 : val_mem segs (rd W (ms_mem ms1)) (f + 8) 8 rp).
    { apply (val_of_chunk_ok segs _ _ _ 8 8%N (SOff 32 0) rp CK8);
      [cbn [sv_denot]; rewrite HE32; unfold w64; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
    assert (N16 : val_mem segs (rd W (ms_mem ms1)) (f + 16) 8 re).
    { apply (val_of_chunk_ok segs _ _ _ 16 8%N (SOff 33 0) re CK16);
      [cbn [sv_denot]; rewrite HE33; unfold w64; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
    assert (N136 : val_mem segs (rd W (ms_mem ms1)) (f + 136) 4 U32M1).
    { apply (frd_chunk_val4 _ _ _ _ _ CK136). intros i Hi.
      cbn [sv_denot]. rewrite HE35.
      destruct Hmdcase as [-> | ->]; unfold U32M1;
      (assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia);
      destruct Hi' as [-> | [-> | [-> | ->]]]; apply bv_eq; vm_compute; reflexivity. }
    assert (AGimg : forall a, in_img segs a -> aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Hi. pose proof (segs_low a Hi) as Hlo. apply UN; [unfold kLowMemEnd in Hlo; lia|].
      unfold ZS. intros Hz. destruct Hz as [Hz | Hz]; [unfold kLowMemEnd in Hlo; lia|].
      apply (blk_img segs B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK a HAR Hblkf); [|exact Hi].
      rewrite RQ. change SRC_FILE_BLOCK with 1304 in *. lia. }
    assert (FAv : forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) ->
      aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Ha Hn. destruct (Z_lt_le_dec a (f + 16)) as [Hl | Hl]; [destruct (Z_lt_le_dec a (f + 8)) as [Hl2 | Hl2]|].
      - apply UN; [change SRC_FILE_BLOCK with 1304 in *; lia|]. unfold ZS. change SRC_FILE_BLOCK with 1304 in *. lia.
      - apply (fr_val_mem_aview_eq (w_H W) memc (ms_mem ms1) (f + 8) 8 rp M8 N8). cbn. lia.
      - apply UN; [change SRC_FILE_BLOCK with 1304 in *; lia|]. unfold ZS. change SRC_FILE_BLOCK with 1304 in *. lia. }
    assert (FA : forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) ->
      mbyte segs (rd W (ms_mem ms1)) a = mbyte segs (rd W memc) a).
    { intros a Ha Hn. apply (mbyte_of_aview segs). apply FAv; assumption. }
    assert (BA : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W (ms_mem ms1)) a = mbyte segs (rd W memc) a).
    { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
      pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
      intros a Ha. apply (mbyte_of_aview segs). apply UN; [lia|]. unfold ZS.
      change SRC_FILE_BLOCK with 1304 in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
    assert (EA : forall a, asrc_env_addr K a -> mbyte segs (rd W (ms_mem ms1)) a = mbyte segs (rd W memc) a).
    { intros a Ha. apply (mbyte_of_aview segs). apply AGimg.
      apply (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))). }
    assert (OA : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W (ms_mem ms1)) a = mbyte segs (rd W memc) a).
    { intros a Ha. apply (mbyte_of_aview segs). apply AGimg.
      apply (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))). }
    (* the window is empty on this path (rpos = rend), so the stream is unbuffered at entry *)
    assert (Hw0 : Z.of_nat (length Wl) = 0).
    { pose proof Hc as Hcp. cbn [branch_taken sv_denot] in Hcp. rewrite HE32, HE33 in Hcp.
      unfold w64 in Hcp. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in Hcp.
      apply bv_eqb_eq in Hcp. apply (f_equal bv_unsigned) in Hcp.
      rewrite !unsigned_lit_small in Hcp by lia. lia. }
    assert (HWlnil : Wl = []) by (apply length_zero_iff_nil; lia).
    rewrite HWlnil in HWIN.
    assert (Hunbuf0 : asource_unbuffered segs K (rd W memc) f b C p) by (split; [exact HSRC0 | exact HWIN]).
    assert (Hunbuf : asource_unbuffered segs K (rd W (ms_mem ms1)) f b C p).
    { apply (asource_unbuffered_frame_mode segs K (rd W memc) (rd W (ms_mem ms1)) f b C p U32M1 FA
        ltac:(split; [exact N136 | right; reflexivity]) BA EA OA Hunbuf0). }
    assert (Hfl' : source_flags segs (rd W (ms_mem ms1)) f fl).
    { apply (source_flags_frame segs (rd W memc) (rd W (ms_mem ms1)) f fl);
        [intros x Hx; apply FA; [change SRC_FILE_BLOCK with 1304 in *; lia | lia] | exact HFL]. }
    (* the live registers at the call state *)
    lreg HS0 (1%bv : bv 5) R1.
    assert (Rra : getr (ms_regs ms1) 1%bv = Z_to_bv 64 (val A_TEXT + 168))
      by (rewrite R1; exact (fr_codeptr_val val _ 168 HEI0)).
    lreg HS0 (2%bv : bv 5) R2.
    lreg HS0 (3%bv : bv 5) R3.
    lreg HS0 (4%bv : bv 5) R4.
    lreg HS0 (8%bv : bv 5) R8.
    lreg HS0 (10%bv : bv 5) R10.
    assert (U2sp : bv_unsigned (ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 2) = spZ regs) by exact VB2.
    assert (Hspc : spZ (ms_regs ms1) = spZ regs - 64).
    { change (spZ (ms_regs ms1)) with (bv_unsigned (getr (ms_regs ms1) 2%bv)). rewrite R2. cbn [sv_denot]. rewrite U2sp.
      rewrite unsigned_lit_small by lia. lia. }
    assert (Rgp : getr (ms_regs ms1) 3%bv = w64 (as_gp B)).
    { rewrite R3. cbn [sv_denot]. rewrite (Eimg_low val _ 3%nat ltac:(cbv [A_TEXT]; lia)),
        (ew_Ereg_nat regs _ 3 3%bv eq_refl), Hgp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (Rtp : getr (ms_regs ms1) 4%bv = w64 (as_tp B)).
    { rewrite R4. cbn [sv_denot]. rewrite (Eimg_low val _ 4%nat ltac:(cbv [A_TEXT]; lia)),
        (ew_Ereg_nat regs _ 4 4%bv eq_refl), Htp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (Ra0 : getr (ms_regs ms1) 10%bv = w64 f).
    { rewrite R10. cbn [sv_denot]. rewrite (Eimg_low val _ 13%nat ltac:(cbv [A_TEXT]; lia)),
        (ew_Ereg_nat regs _ 13 13%bv eq_refl), G13. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (Rs0v : getr (ms_regs ms1) 8%bv = w64 f).
    { rewrite R8. cbn [sv_denot]. rewrite (Eimg_low val _ 13%nat ltac:(cbv [A_TEXT]; lia)),
        (ew_Ereg_nat regs _ 13 13%bv eq_refl), G13. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (Rs0 : s0Z (ms_regs ms1) = f)
      by (unfold s0Z; rewrite Rs0v; unfold w64; apply fa_u64_small; change SRC_FILE_BLOCK with 1304 in *; lia).
    assert (Hra_rng : 0 <= val A_TEXT + 168 < 2 ^ 64) by (destruct HBok as (_ & Hhi & _); lia).
    assert (Hra_ev : (val A_TEXT + 168) mod 2 = 0).
    { destruct HBok as (_ & _ & Hm4).
      pose proof (Z_div_mod_eq_full (val A_TEXT) 4) as Hd. rewrite Hm4, Z.add_0_r in Hd.
      rewrite Hd. replace (4 * (val A_TEXT / 4) + 168) with ((2 * (val A_TEXT / 4) + 84) * 2) by ring.
      apply Z_mod_mult. }
    assert (Hret1 : YK0s.ret_ok (getr (ms_regs ms1) 1%bv)).
    { unfold YK0s.ret_ok. rewrite Rra. unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by exact Hra_rng.
      rewrite Z.add_0_r. rewrite YK0s.land_m2_even by exact Hra_ev. reflexivity. }
    assert (Hra4096 : 4096 <= val A_TEXT + 168 < 2 ^ 64) by (split; [pose proof Hbase_lo; lia | exact (proj2 Hra_rng)]).
    (* the __toread call *)
    lazymatch type of HS0 with st_ok ?sg ?Ev ?ssx (restrict ?HH ?msr) =>
      rewrite (st_ok_restrict_mkst sg HH Ev ssx msr HS0 ltac:(vm_compute; reflexivity));
      replace (ss_pc ssx) with (sigma FS_toread) by (vm_compute; reflexivity) end.
    eapply SRr_bind.
    { apply (frd_call_toread segs B K LAWS segs_low (sigma FS_toread) HTOREAD
               STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) _ k regs (ms_regs ms1) []
               f b p fl (val A_TEXT + 168) C HJ Hspc Hal16 Hstk1 Hsple Rra
               Hret1 Hra4096
               Rgp Rtp
               ltac:(apply achain_low; rewrite Rs0; change SRC_FILE_BLOCK with 1304 in *; lia)
               Ra0 Hblkf Hblkb Hbstk Hunbuf Hfl' HWRF). }
    intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & Hcfg & HJ2 & HJtoread & HPpres & Htopost).
    subst c2. rewrite Rra.
    destruct Htopost as (-> & -> & Ha0t & Hunb2 & Hfl2 & Hmd2 & Hrp2 & Hre2 & Hband2). (* POS *)
    pose proof HJtoread as (_ & _ & _ & _ & Hiot & _ & _ & _ & G1t & _ & _ & _ & _ & _ & Hstkt & _ & _).
    pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _ & _ & _).
    pose proof HJ as (HARc & _).
    assert (KST : forall a, spZ regs + -64 <= a < spZ regs + 0 ->
      aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms1) a).
    { intros a Ha. apply G1t.
      - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
      - rewrite Hspc. lia. }
    assert (KPR : forall a, spZ regs + -64 <= a < spZ regs + 0 -> apresent (w_H W2) mem2 a).
    { intros a Ha. apply Hpres2. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
    (* what the path kept up to here: the runs to the call kept every byte outside fread's frame
       and the two FILE windows; __toread kept what its journal keeps, clause by clause *)
    assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RFREAD_STK <= a < spZ regs) -> ~ rread_wrset f d nm a ->
      aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Ha Hw Hwr. apply UN; [exact Ha|]. unfold ZS. intros Hz. unfold rread_wrset in Hwr.
      change SRC_FILE_BLOCK with 1304 in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hw. lia. }
    assert (APG1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a).
    { intros a Ha. apply (fr_apresent_grows _ (ms_mem ms0)); [exact HG1|].
      apply (fr_apresent_grows _ (ms_mem ms)); [exact HG0|].
      apply (fr_apresent_grows _ memc); [exact HG|exact Ha]. }
    assert (APW1 : forall a, spZ regs - RFREAD_STK <= a < spZ regs -> apresent (w_H W) (ms_mem ms1) a).
    { intros a Ha. apply APG1. apply Hpres0. lia. }
    assert (K1 : rread_kept segs B RFREAD_STK lyc Sc W memc W (ms_mem ms1) (spZ regs) (rread_wrset f d nm)).
    { apply (frd_kept_of_agree_all segs B LAWS RFREAD_STK lyc Sc W memc mdc W (ms_mem ms1) (spZ regs) (rread_wrset f d nm) HAR);
      [unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia | exact AG1 | exact AGimg | exact APG1 | exact APW1]. }
    assert (Hcl : ~ YI16.sink_open_fp (rtoread_fp f))
      by (apply sink_closed_pos; constructor; [cbn [fst]; lia | constructor]).
    assert (K2 : rread_kept segs B RTOREAD_STK lyc Sc W (ms_mem ms1) W2 mem2 (spZ (ms_regs ms1))
                   (fun a => f <= a < f + SRC_FILE_BLOCK)).
    { apply (frd_kept_of_acall segs B).
      apply (acall_kept_of_journal segs B segs_low RTOREAD_STK (spZ (ms_regs ms1)) (rtoread_fp f) [] lyc Sc W (ms_mem ms1) _
               lyc Sc W2 mem2 md2 0 (fun a => f <= a < f + SRC_FILE_BLOCK) HJtoread HARc); [| | exact Hcl].
      - intros a (r & Hr & Ha). unfold rtoread_fp in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact Ha.
      - intros bb m i Hb _ _. exact Hb. }
    assert (K12 : rread_kept segs B RFREAD_STK lyc Sc W memc W2 mem2 (spZ regs) (rread_wrset f d nm)).
    { apply (frd_kept_trans segs B RFREAD_STK RTOREAD_STK RFREAD_STK lyc Sc W memc W (ms_mem ms1) W2 mem2
               (spZ regs) (spZ (ms_regs ms1)) (spZ regs) (rread_wrset f d nm) (fun a => f <= a < f + SRC_FILE_BLOCK)
               (rread_wrset f d nm) K1 K2).
      - lia.
      - lia.
      - rewrite Hspc. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK. lia.
      - rewrite Hspc. lia.
      - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
      - lia.
      - intros a Ha. apply Hpres0. lia.
      - intros a Ha. exact Ha.
      - intros a Ha. left. exact Ha. }
    assert (BAND1 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
      aview segs (w_H W) (ms_mem ms1) s = aview segs (w_H W) memc s).
    { apply (frd_band_of_low segs B LAWS lyc Sc W memc mdc W (ms_mem ms1) f d nm HAR Hblkf Hdam).
      intros a Ha Hn. apply AG1; [lia | unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia | exact Hn]. }
    assert (BAND12 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
      aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s)
      by (intros s Hs; rewrite (Hband2 s Hs); exact (BAND1 s Hs)).
    destruct (aos_step_closed _ _ _ Hcl Hiot) as (Hfd2 & Hfs2 & _ & _).
    assert (Hfds2 : m_fds md2 = m_fds mdc) by (unfold m_fds; rewrite Hfd2; reflexivity).
    assert (Hfss2 : m_fs md2 = m_fs mdc) by (unfold m_fs; rewrite Hfs2; reflexivity).
    assert (Hnm1 : nm <> 0).
    { intros Hz. pose proof Hc2 as Hcp. cbn [branch_taken sv_denot] in Hcp. rewrite HE12, HE11 in Hcp.
      unfold w64 in Hcp. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in Hcp.
      rewrite m_mul, v_mul_one in Hcp by lia. rewrite Hz in Hcp. vm_compute in Hcp. discriminate. }
    (* reseat at the return 0x8ef04: keep fread's frame, havoc the caller-saved registers *)
    lazymatch type of HS0 with st_ok _ ?Ev ?ssc ?msc =>
      let rs := eval vm_compute in (pick (ss_mem ssc) [0%nat]) in
      assert (Hkept : Forall (region_kept segs Ev (ms_mem msc) (mrestrict (w_H W2) mem2)) rs)
        by (cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
            apply (frd_region_kept Ev W W2 (ms_mem ms1) mem2 2%nat (spZ regs)); [exact U2sp | exact KST | exact KPR]);
      pose proof (fr_after_call segs val 40%nat Ev ssc msc regs2 (mrestrict (w_H W2) mem2) rs 168
        HEI0 ltac:(lia) HS0 ltac:(vm_compute; reflexivity) ltac:(cbv; lia)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HPpres Hkept) as HSa;
      let ss2 := eval vm_compute in (ss_after_call ssc rs 40 168) in
      change (ss_after_call ssc rs 40 168) with ss2 in HSa
    end.
    rewrite <- restrict_mkst_fx in HSa.
    clear HS0 Hkept R1 R2 R3 R4 R8 R10 Rgp Rtp Ra0 Rs0v Rs0 Hra_rng Hra_ev Hret1 Hra4096.
    pose proof (fr_img_env_havoc val _ 40 (map (getr regs2) CLOB) HEI0 ltac:(rewrite length_map; cbv; lia)) as HEIa.
    pose proof (frd_base_havoc _ 40 (map (getr regs2) CLOB) 13 f ltac:(lia) VB13) as VB13a.
    pose proof (frd_base_havoc _ 40 (map (getr regs2) CLOB) 2 (spZ regs) ltac:(lia) VB2) as VB2a.
    assert (HE34 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 34 = w64 (as_read K))
      by (rewrite (Eimg_low val _ 34%nat ltac:(cbv [A_TEXT]; lia)); exact (ew_Ereg_extra regs _ 2)).
    pose proof (frd_ew_havoc _ 40 (map (getr regs2) CLOB) 34 _ ltac:(lia) HE34) as HE34a.
    pose proof Hunb2 as ((Wl2 & cpos2 & fl2 & md2' & _ & _ & _ & _ & _ & _ & _ & _ & _ & HST2 & _) & Hwin2). (* POS *)
    pose proof HST2 as (_ & Hread2 & _).
    (* the FILE cell the code reads next: f->read at +64 *)
    pose proof (fr_add_region segs val _ _ _
      (YP09.mkRegion (Some 13%nat) 0 1304 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 34 0))]) HSa
      ltac:(vm_compute; reflexivity)) as HSb.
    lazymatch type of HSb with ?A -> _ => assert (HR3 : A) end.
    { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
      rewrite VB13a. split; [lia|]. split; [change SRC_FILE_BLOCK with 1304 in *; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs _ _ f 64 8%N (SOff 34 0) (as_read K));
        [cbn [sv_denot]; rewrite HE34a; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; destruct Hmread_pc; lia | cbn; lia | exact Hread2]. }
    specialize (HSb HR3).
    lazymatch type of HSb with ?A -> _ => assert (HD3 : A) end.
    { cbn [ss_mem all_disjoint]. repeat apply conj; try exact I;
      (unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?VB2a, ?VB13a;
       change SRC_FILE_BLOCK with 1304 in *; first [left; lia | right; lia]). }
    specialize (HSb HD3).
    clear HSa HR3 HD3.
    lazymatch type of HSb with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HSb end.
    clear SHOK.
    assert (SHOK : sh_ok segs (SLit 0) (@nil shent)
      (havoc (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 40 (map (getr regs2) CLOB)) (mrestrict (w_H W2) mem2))
      by apply Forall_nil.
    rename HSb into HS0. clear HJ. rename HJ2 into HJ.
    (* 0x8ef04 bnez a0: a0 = (fl == 24 ? -1 : 0) *)
    pose proof (frd_ew_havoc _ 40 (map (getr regs2) CLOB) 12 _ ltac:(lia) HE12) as HE12a.
    pose proof (frd_ew_havoc _ 40 (map (getr regs2) CLOB) 11 _ ltac:(lia) HE11) as HE11a.
    destruct (proj2 Hfl2) as [Hfl8 | Hfl24]; subst fl.
    * (* fl = 8: __toread returned 0, fall through to f->read *)
      frd_branch_auto; clear HS0; intros Hc3 HS0.
      -- exfalso. cbn [branch_taken sv_denot havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB] in Hc3.
         rewrite Ha0t in Hc3. vm_compute in Hc3. discriminate.
      -- frd_run RUNF HS0 HJ SHOK.
         { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
           destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
           rewrite ?VB2a, ?VB13a in Hr0; [lia | apply AWRgen; lia]. }
         (* 0x8ef04 - 0x8ef18 wrote only fread's frame *)
         set (ZS4 := fun a => spZ regs - 64 <= a < spZ regs).
         pose proof (fr_kept_of_frame segs _ _ (w_H W2) _ _ ZS4 HFr2
           ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                 repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2a, ?VB13a in Hrr; unfold ZS4; lia|]);
                 destruct Hin)) as UN4.
         pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _ & _ & _).
         assert (FA4 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W2 (ms_mem ms2)) a = mbyte segs (rd W2 mem2) a).
         { intros a Ha. apply (mbyte_of_aview segs). apply UN4; [change SRC_FILE_BLOCK with 1304 in *; lia|].
           unfold ZS4. change SRC_FILE_BLOCK with 1304 in *. lia. }
         assert (BA4 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W2 (ms_mem ms2)) a = mbyte segs (rd W2 mem2) a).
         { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
           pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
           intros a Ha. apply (mbyte_of_aview segs). apply UN4; [lia|]. unfold ZS4.
           unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
         assert (EA4 : forall a, asrc_env_addr K a -> mbyte segs (rd W2 (ms_mem ms2)) a = mbyte segs (rd W2 mem2) a).
         { intros a Ha. apply (mbyte_of_aview segs).
           pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
           pose proof (segs_low a Hi) as Hl. apply UN4; [unfold kLowMemEnd in Hl; lia|]. unfold ZS4.
           unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
         assert (OA4 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W2 (ms_mem ms2)) a = mbyte segs (rd W2 mem2) a).
         { intros a Ha. apply (mbyte_of_aview segs).
           pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
           pose proof (segs_low a Hi) as Hl. apply UN4; [unfold kLowMemEnd in Hl; lia|]. unfold ZS4.
           unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
         assert (Hunbm : asource_unbuffered segs K (rd W2 (ms_mem ms2)) f b C p)
           by exact (asource_unbuffered_frame segs K (rd W2 mem2) (rd W2 (ms_mem ms2)) f b C p FA4 BA4 EA4 OA4 Hunb2).
         assert (Hflm : source_flags segs (rd W2 (ms_mem ms2)) f 8).
         { apply (source_flags_frame segs (rd W2 mem2) (rd W2 (ms_mem ms2)) f 8); [|exact Hfl2].
           intros x Hx. apply FA4. change SRC_FILE_BLOCK with 1304 in *. lia. }
         assert (Hmdm : source_mode segs (rd W2 (ms_mem ms2)) f U32M1).
         { apply (source_mode_frame segs (rd W2 mem2) (rd W2 (ms_mem ms2)) f U32M1); [|exact Hmd2].
           intros x Hx. apply FA4. change SRC_FILE_BLOCK with 1304 in *. lia. }
         assert (BAND124 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
           aview segs (w_H W2) (ms_mem ms2) s = aview segs (w_H W) memc s).
         { intros s Hs. rewrite (UN4 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND12 s Hs)|].
           unfold ZS4. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
           unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
         assert (K124 : rread_kept segs B RFREAD_STK lyc Sc W memc W2 (ms_mem ms2) (spZ regs) (rread_wrset f d nm)).
         { apply (frd_kept_extend lyc Sc W memc W2 mem2 md2 (ms_mem ms2) (spZ regs) (rread_wrset f d nm) K12 HAR2).
           - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
           - lia.
           - intros a Ha. apply Hpres0. lia.
           - intros a Ha Hs. apply UN4; [exact Ha|]. unfold ZS4. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
           - intros a Ha. exact (fr_apresent_grows _ mem2 (ms_mem ms2) a HG2 Ha).
           - intros a Ha. apply Hpres4. lia. }
         (* 0x8ef18 jalr a3: a3 = f->read = mread *)
         frd_reg HS0 (13%bv : bv 5) R13x.
         assert (R13 : getr (ms_regs ms2) 13%bv = Z_to_bv 64 (as_read K)).
         { rewrite R13x. cbn [sv_denot]. rewrite HE34a. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
         apply (fr_jalr_call segs Hwx tbl tbl_ok val sigma frd_listing Hcert HBok W2 _ _ _ _ _ 0x680e7 1%bv 13%bv (as_read K)
                  HEIa HS0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) frd_D_jalr ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) R13 (proj1 Hmread_pc) (proj2 Hmread_pc)).
         intros matJ msm Hmsm HSm. subst msm.
         lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ _ _; cfg_model := _ |} _ => set (regsm := rg) in * end.
         lreg HSm (1%bv : bv 5) Q1. cbn [ms_regs mkst] in Q1.
         lreg HSm (2%bv : bv 5) Q2. cbn [ms_regs mkst] in Q2.
         lreg HSm (3%bv : bv 5) Q3. cbn [ms_regs mkst] in Q3.
         lreg HSm (4%bv : bv 5) Q4. cbn [ms_regs mkst] in Q4.
         lreg HSm (8%bv : bv 5) Q8. cbn [ms_regs mkst] in Q8.
         lreg HSm (10%bv : bv 5) Q10. cbn [ms_regs mkst] in Q10.
         lreg HSm (11%bv : bv 5) Q11. cbn [ms_regs mkst] in Q11.
         lreg HSm (12%bv : bv 5) Q12. cbn [ms_regs mkst] in Q12.
         assert (Rram : getr regsm 1%bv = Z_to_bv 64 (val A_TEXT + 192))
           by (rewrite Q1; exact (fr_codeptr_val val _ 192 HEIa)).
         assert (Hspm : spZ regsm = spZ regs - 64).
         { change (spZ regsm) with (bv_unsigned (getr regsm 2%bv)). rewrite Q2. cbn [sv_denot].
           rewrite ew_havoc_old by lia. rewrite U2sp. rewrite unsigned_lit_small by lia. lia. }
         assert (Rgpm : getr regsm 3%bv = w64 (as_gp B)).
         { rewrite Q3. cbn [sv_denot]. rewrite ew_havoc_old by lia. rewrite (Eimg_low val _ 3%nat ltac:(cbv [A_TEXT]; lia)),
             (ew_Ereg_nat regs _ 3 3%bv eq_refl), Hgp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
         assert (Rtpm : getr regsm 4%bv = w64 (as_tp B)).
         { rewrite Q4. cbn [sv_denot]. rewrite ew_havoc_old by lia. rewrite (Eimg_low val _ 4%nat ltac:(cbv [A_TEXT]; lia)),
             (ew_Ereg_nat regs _ 4 4%bv eq_refl), Htp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
         assert (Ra0m : getr regsm 10%bv = w64 f).
         { rewrite Q10. cbn [sv_denot]. rewrite ew_havoc_old by lia. rewrite (Eimg_low val _ 13%nat ltac:(cbv [A_TEXT]; lia)),
             (ew_Ereg_nat regs _ 13 13%bv eq_refl), G13. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
         assert (Rs0vm : getr regsm 8%bv = w64 f).
         { rewrite Q8. cbn [sv_denot]. rewrite ew_havoc_old by lia. rewrite (Eimg_low val _ 13%nat ltac:(cbv [A_TEXT]; lia)),
             (ew_Ereg_nat regs _ 13 13%bv eq_refl), G13. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
         assert (Ra1m : getr regsm 11%bv = w64 d).
         { rewrite Q11. cbn [sv_denot]. rewrite ew_havoc_old by lia. rewrite (Eimg_low val _ 10%nat ltac:(cbv [A_TEXT]; lia)),
             (ew_Ereg_nat regs _ 10 10%bv eq_refl), G10. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
         assert (Ra2m : getr regsm 12%bv = w64 nm)
           by (rewrite Q12, denot_lit_U, (frd_U_a2 _ nm HE12a HE11a Hnm); reflexivity).
         assert (Rs0m : s0Z regsm = f)
           by (unfold s0Z; rewrite Rs0vm; unfold w64; apply fa_u64_small; change SRC_FILE_BLOCK with 1304 in *; lia).
         assert (Hra192 : 0 <= val A_TEXT + 192 < 2 ^ 64) by (destruct HBok as (_ & Hhi & _); lia).
         assert (Hra192e : (val A_TEXT + 192) mod 2 = 0).
         { destruct HBok as (_ & _ & Hm4).
           pose proof (Z_div_mod_eq_full (val A_TEXT) 4) as Hd. rewrite Hm4, Z.add_0_r in Hd.
           rewrite Hd. replace (4 * (val A_TEXT / 4) + 192) with ((2 * (val A_TEXT / 4) + 96) * 2) by ring.
           apply Z_mod_mult. }
         assert (Hretm : YK0s.ret_ok (getr regsm 1%bv)).
         { unfold YK0s.ret_ok. rewrite Rram. unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by exact Hra192.
           rewrite Z.add_0_r. rewrite YK0s.land_m2_even by exact Hra192e. reflexivity. }
         assert (Hra192b : 4096 <= val A_TEXT + 192 < 2 ^ 64) by (split; [pose proof Hbase_lo; lia | exact (proj2 Hra192)]).
         pose proof (conj Hdf (conj Hdb (conj Hd0 (conj Hdam (conj Hdat (conj Hdwr (conj Hdra Hdhull))))))) as HDEST0.
         assert (Hdestm : rread_dest segs B STK sp0 FP ly S own lyc Sc W2 (ms_mem ms2) RFREAD_STK (spZ regs) d nm f b
                            (Z.of_nat (length C))).
         { apply (frd_dest_sub segs B STK sp0 FP ly S own lyc Sc W memc W2 (ms_mem ms2) RFREAD_STK (spZ regs) RFREAD_STK (spZ regs)
                    d nm d nm f b (Z.of_nat (length C)) HDEST0); try lia. exact BAND124. }
         pose proof (ajournal_materialize segs B LAWS segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 (ms_mem ms2) _ k matJ HJ)
           as HJm.
         (* the mread call *)
         eapply SRr_bind.
         { apply (frd_call_mread segs B K HMREAD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 (ms_mem ms2) _ k regs regsm []
                    d nm d nm f b p U32M1 (val A_TEXT + 192) C
                    HJm Hspm Hal16 Hstk1 Hsple Rram Hretm Hra192b Rgpm Rtpm
                    ltac:(apply achain_low; rewrite Rs0m; change SRC_FILE_BLOCK with 1304 in *; lia)
                    Ra0m Ra1m Ra2m Hblkf Hblkb Hbstk Hunbm Hflm Hmdm HWRF ltac:(lia) Hdestm ltac:(lia) ltac:(lia)). }
         intros W3 c3 Hle3 (ly3 & S3 & regs3 & mem3 & md3 & Hcfg3 & HJ3 & HPpres3 & Kmr & Hmrpost).
         subst c3. rewrite Rram.
         destruct Hmrpost as (-> & -> & Ha0m & Hgarrm & Hatm & Hcookm & Hrpm & Hrem & Hflm3 & Hmdm3 & Hfdsm & Hfsm & Hbandm). (* POS *)
         pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _ & _ & _).
         pose proof Kmr as (Kmr1 & _).
         assert (KST3 : forall a, spZ regs + -64 <= a < spZ regs + 0 ->
           aview segs (w_H W3) mem3 a = aview segs (w_H W2) (ms_mem ms2) a).
         { intros a Ha. apply Kmr1.
           - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
           - rewrite Hspm. unfold RMREAD_STK, ESTACK. lia.
           - unfold rread_wrset. intros [Hx | Hx]; [change SRC_FILE_BLOCK with 1304 in *; lia|].
             apply (proj2 (Hdwr a Hx)). unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK. lia. }
         assert (KPR3 : forall a, spZ regs + -64 <= a < spZ regs + 0 -> apresent (w_H W3) mem3 a).
         { intros a Ha. apply Hpres3. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
         (* reseat at the return 0x8ef1c: keep fread's frame; the FILE is not read again on these paths *)
         lazymatch type of HSm with st_ok _ ?Ev ?ssc ?msc =>
           let rs := eval vm_compute in (pick (ss_mem ssc) [1%nat]) in
           assert (Hkept3 : Forall (region_kept segs Ev (ms_mem msc) (mrestrict (w_H W3) mem3)) rs)
             by (cbn [ms_mem restrict mkst]; apply Forall_cons; [|apply Forall_nil];
                 apply (frd_region_kept Ev W2 W3 (ms_mem ms2) mem3 2%nat (spZ regs)); [exact VB2a | exact KST3 | exact KPR3]);
           pose proof (fr_after_call segs val 64%nat Ev ssc msc regs3 (mrestrict (w_H W3) mem3) rs 192
             HEIa ltac:(lia) HSm ltac:(vm_compute; reflexivity) ltac:(cbv; lia)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HPpres3 Hkept3) as HSc;
           let ss3 := eval vm_compute in (ss_after_call ssc rs 64 192) in
           change (ss_after_call ssc rs 64 192) with ss3 in HSc
         end.
         rewrite <- restrict_mkst_fx in HSc.
         clear HSm Hkept3 HS0.
         pose proof (fr_img_env_havoc val _ 64 (map (getr regs3) CLOB) HEIa ltac:(rewrite length_map; cbv; lia)) as HEIb.
         pose proof (frd_base_havoc _ 64 (map (getr regs3) CLOB) 13 f ltac:(lia) VB13a) as VB13b.
         pose proof (frd_base_havoc _ 64 (map (getr regs3) CLOB) 2 (spZ regs) ltac:(lia) VB2a) as VB2b.
         pose proof (frd_ew_havoc _ 64 (map (getr regs3) CLOB) 12 _ ltac:(lia) HE12a) as HE12b.
         pose proof (frd_ew_havoc _ 64 (map (getr regs3) CLOB) 11 _ ltac:(lia) HE11a) as HE11b.
         lazymatch type of HSc with st_ok_pi _ _ ?E3 _ _ =>
           clear SHOK; assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W3) mem3)) by apply Forall_nil end.
         rename HSc into HS0. clear HJ. rename HJ3 into HJ.
         (* what the path kept through mread *)
         assert (K1245 : rread_kept segs B RFREAD_STK lyc Sc W memc W3 mem3 (spZ regs) (rread_wrset f d nm)).
         { apply (frd_kept_trans segs B RFREAD_STK RMREAD_STK RFREAD_STK lyc Sc W memc W2 (ms_mem ms2) W3 mem3
                    (spZ regs) (spZ regsm) (spZ regs) (rread_wrset f d nm) (rread_wrset f d nm) (rread_wrset f d nm) K124 Kmr).
           - lia.
           - lia.
           - rewrite Hspm. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK. lia.
           - rewrite Hspm. lia.
           - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
           - lia.
           - intros a Ha. apply Hpres0. lia.
           - intros a Ha. exact Ha.
           - intros a Ha. exact Ha. }
         assert (BAND1245 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
           aview segs (w_H W3) mem3 s = aview segs (w_H W) memc s)
           by (intros s Hs; rewrite (Hbandm s Hs); exact (BAND124 s Hs)).
         assert (Hfds3 : m_fds md3 = m_fds mdc) by (rewrite Hfdsm; exact Hfds2).
         assert (Hfss3 : m_fs md3 = m_fs mdc) by (rewrite Hfsm; exact Hfss2).
         pose proof (rread_k_bounds nm (Z.of_nat (length C)) p ltac:(lia) ltac:(lia)) as Hkb.
         (* 0x8ef1c beqz a0: a0 = k = min(nm, |C| - p) *)
         frd_branch_auto; clear HS0; intros Hc4 HS0.
         ++ (* k = 0: return (s6 - s4) / s1 = 0 *)
            assert (Hj0 : rread_k nm (Z.of_nat (length C)) p = 0).
            { pose proof Hc4 as Hcp. cbn [branch_taken sv_denot havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB] in Hcp.
              rewrite Ha0m in Hcp. unfold w64 in Hcp. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hcp.
              apply bv_eqb_eq in Hcp. apply (f_equal bv_unsigned) in Hcp.
              rewrite !unsigned_lit_small in Hcp by lia. exact Hcp. }
            frd_run RUNF HS0 HJ SHOK.
            { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
              destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
              rewrite ?VB2b in Hr0; apply AWRgen; lia. }
            eapply (RETF W3 _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity)).
            intros matR.
            set (ZS5 := fun a => spZ regs - 64 <= a < spZ regs).
            pose proof (fr_kept_of_frame segs _ _ (w_H W3) _ _ ZS5 HFr3
              ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2b in Hrr; unfold ZS5; lia|]);
                    destruct Hin)) as UN5.
            pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & _ & _ & _).
            frd_reg HS0 (1%bv : bv 5) R1x.
            assert (R1 : getr (ms_regs ms3) 1 = getr regs 1).
            { rewrite R1x. cbn [sv_denot]. rewrite !ew_havoc_old by lia.
              rewrite (Eimg_low val _ 1%nat ltac:(cbv [A_TEXT]; lia)), (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r.
              apply Z_to_bv_bv_unsigned. }
            assert (HPR : aregs_preserved regs (ms_regs ms3)).
            { lazymatch type of HS0 with st_ok_pi _ _ ?E ?ss _ =>
                exact (aregs_preserved_of_st_ok segs (w_H W3) E (abs_ss val ss) ms3 regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]
                         HS0 (frd_ea_havoc2 _ _ 64 _ (frd_ea_havoc val regs _ 40 _ ltac:(lia)) ltac:(lia))
                         ltac:(vm_compute; reflexivity)) end. }
            frd_reg HS0 (10%bv : bv 5) R10x.
            assert (R10 : getr (ms_regs ms3) 10 = w64 0).
            { rewrite R10x, denot_lit_U, (frd_U_ret0 _ nm HE12b HE11b Hnm). reflexivity. }
            assert (FA5 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W3 (ms_mem ms3)) a = mbyte segs (rd W3 mem3) a).
            { intros a Ha. apply (mbyte_of_aview segs). apply UN5; [change SRC_FILE_BLOCK with 1304 in *; lia|].
              unfold ZS5. change SRC_FILE_BLOCK with 1304 in *. lia. }
            assert (BA5 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W3 (ms_mem ms3)) a = mbyte segs (rd W3 mem3) a).
            { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
              pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
              intros a Ha. apply (mbyte_of_aview segs). apply UN5; [lia|]. unfold ZS5.
              unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
            assert (EA5 : forall a, asrc_env_addr K a -> mbyte segs (rd W3 (ms_mem ms3)) a = mbyte segs (rd W3 mem3) a).
            { intros a Ha. apply (mbyte_of_aview segs).
              pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
              pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
              unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
            assert (OA5 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W3 (ms_mem ms3)) a = mbyte segs (rd W3 mem3) a).
            { intros a Ha. apply (mbyte_of_aview segs).
              pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
              pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
              unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
            assert (HAT : asource_at segs K (rd W3 (ms_mem ms3)) f b C (p + rread_k nm (Z.of_nat (length C)) p))
              by exact (asource_at_frame segs K (rd W3 mem3) (rd W3 (ms_mem ms3)) f b C _ FA5 BA5 EA5 OA5 Hatm).
            assert (HMD5 : source_mode segs (rd W3 (ms_mem ms3)) f U32M1).
            { apply (source_mode_frame segs (rd W3 mem3) (rd W3 (ms_mem ms3)) f U32M1); [|exact Hmdm3].
              intros a Ha. apply FA5. change SRC_FILE_BLOCK with 1304 in *. lia. }
            assert (KF : rread_kept segs B RFREAD_STK lyc Sc W memc W3 (ms_mem ms3) (spZ regs) (rread_wrset f d nm)).
            { apply (frd_kept_extend lyc Sc W memc W3 mem3 md3 (ms_mem ms3) (spZ regs) (rread_wrset f d nm) K1245 HAR3).
              - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
              - lia.
              - intros a Ha. apply Hpres0. lia.
              - intros a Ha Hs. apply UN5; [exact Ha|]. unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
              - intros a Ha. exact (fr_apresent_grows _ mem3 (ms_mem ms3) a HG3 Ha).
              - intros a Ha. apply HpresF. lia. }
            unfold rread_post_base.
            eexists lyc, Sc, (ms_regs ms3), (ms_mem ms3), _.
            split; [rewrite R1, (fr_ret_of_ok _ Hra); reflexivity|].
            split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ|].
            split; [exact HPR|].
            split; [exact KF|].
            unfold rfread_post. cbv zeta.
            split; [reflexivity|]. split; [reflexivity|].
            split; [rewrite Hj0; exact R10|].
            split; [rewrite Hj0; apply frd_garr8_firstn_nil|].
            split; [exact HAT|].
            split; [exact HMD5|].
            split; [intros Hz; exfalso; exact (Hnm1 Hz)|].
            split; [exact Hfds3|]. split; [exact Hfss3|].
            intros s Hs. rewrite (UN5 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND1245 s Hs)|].
            unfold ZS5. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
            unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
         ++ (* k <> 0: s4 -= k, then 0x8ef28 bnez s4 *)
            frd_run RUNF HS0 HJ SHOK.
            { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
              destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
              rewrite ?VB2b in Hr0; apply AWRgen; lia. }
            frd_branch_auto; clear HS0; intros Hc5 HS0.
            ** (* s4 <> 0: k < nm, so |C| - p < nm: mread set F_EOF and left the window empty; back to __toread *)
               lazymatch type of HE12b with ew ?E3 _ = _ =>
                 assert (HE68 : ew E3 68 = w64 (rread_k nm (Z.of_nat (length C)) p))
                   by (cbn [havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB]; exact Ha0m) end.
               assert (Hjlt : rread_k nm (Z.of_nat (length C)) p < nm).
               { pose proof Hc5 as Hcp. rewrite !denot_lit_U in Hcp.
                 rewrite (frd_U_s4k _ nm _ HE12b HE11b HE68 Hnm ltac:(lia)), U_SLit in Hcp.
                 rewrite (zcanon_id 0) in Hcp by (unfold M64; lia).
                 cbn [branch_taken] in Hcp. apply Bool.negb_true_iff in Hcp.
                 destruct (Z.eq_dec (rread_k nm (Z.of_nat (length C)) p) nm) as [He|He]; [|lia].
                 exfalso. rewrite He, Z.sub_diag in Hcp. vm_compute in Hcp. discriminate. }
               assert (Hjnp : rread_k nm (Z.of_nat (length C)) p = Z.of_nat (length C) - p) by (unfold rread_k in *; lia).
               assert (Hfill0 : rmread_fill nm (Z.of_nat (length C)) p = 0)
                 by (unfold rmread_fill; rewrite Hjnp; unfold SRC_BUFSIZ; lia).
               assert (Hgt : (nm >? Z.of_nat (length C) - p) = true) by (apply Z.gtb_lt; lia).
               rewrite Hgt in Hflm3. rewrite Hfill0, Z.add_0_r in Hrem.
               frd_run RUNF HS0 HJ SHOK.
               { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
                 destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
                 rewrite ?VB2b in Hr0; apply AWRgen; lia. }
               (* 0x8ef1c - 0x8ef00 wrote only fread's frame *)
               set (ZS5 := fun a => spZ regs - 64 <= a < spZ regs).
               pose proof (fr_kept_of_frame segs _ _ (w_H W3) _ _ ZS5 HFr3
                 ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                       repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2b in Hrr; unfold ZS5; lia|]);
                       destruct Hin)) as U5.
               pose proof (fr_kept_of_frame segs _ _ (w_H W3) _ _ ZS5 HFr4
                 ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                       repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2b in Hrr; unfold ZS5; lia|]);
                       destruct Hin)) as U6.
               assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ ZS5 a -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a)
                 by (intros a Ha Hz; rewrite (U6 a Ha Hz), (U5 a Ha Hz); reflexivity).
               clear U5 U6.
               pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _ & _ & _).
               assert (FA5 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W3 (ms_mem ms4)) a = mbyte segs (rd W3 mem3) a).
               { intros a Ha. apply (mbyte_of_aview segs). apply UN5; [change SRC_FILE_BLOCK with 1304 in *; lia|].
                 unfold ZS5. change SRC_FILE_BLOCK with 1304 in *. lia. }
               assert (BA5 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W3 (ms_mem ms4)) a = mbyte segs (rd W3 mem3) a).
               { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
                 pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
                 intros a Ha. apply (mbyte_of_aview segs). apply UN5; [lia|]. unfold ZS5.
                 unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
               assert (EA5 : forall a, asrc_env_addr K a -> mbyte segs (rd W3 (ms_mem ms4)) a = mbyte segs (rd W3 mem3) a).
               { intros a Ha. apply (mbyte_of_aview segs).
                 pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
                 pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
                 unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
               assert (OA5 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W3 (ms_mem ms4)) a = mbyte segs (rd W3 mem3) a).
               { intros a Ha. apply (mbyte_of_aview segs).
                 pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
                 pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
                 unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
               (* rpos = rend = f + 280: the window is empty (r = 0 on a short read) *)
               assert (Hwin3 : source_window segs (rd W3 mem3) f []).
               { right. exists 0. split; [lia|]. split; [cbn [length Z.of_nat]; unfold SRC_BUFSIZ; lia|].
                 split; [rewrite Z.add_0_r; exact Hrpm|]. split; [cbn [length Z.of_nat]; rewrite !Z.add_0_r; exact Hrem|].
                 apply garr8_nil. }
               assert (Hunb5 : asource_unbuffered segs K (rd W3 (ms_mem ms4)) f b C (p + rread_k nm (Z.of_nat (length C)) p))
                 by exact (asource_unbuffered_frame segs K (rd W3 mem3) (rd W3 (ms_mem ms4)) f b C _ FA5 BA5 EA5 OA5 (conj Hatm Hwin3)).
               assert (Hfl5 : source_flags segs (rd W3 (ms_mem ms4)) f 24).
               { apply (source_flags_frame segs (rd W3 mem3) (rd W3 (ms_mem ms4)) f 24); [|exact Hflm3].
                 intros x Hx. apply FA5. change SRC_FILE_BLOCK with 1304 in *. lia. }
               assert (K6 : rread_kept segs B RFREAD_STK lyc Sc W memc W3 (ms_mem ms4) (spZ regs) (rread_wrset f d nm)).
               { apply (frd_kept_extend lyc Sc W memc W3 mem3 md3 (ms_mem ms4) (spZ regs) (rread_wrset f d nm) K1245 HAR3).
                 - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
                 - lia.
                 - intros a Ha. apply Hpres0. lia.
                 - intros a Ha Hs. apply UN5; [exact Ha|]. unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
                 - intros a Ha. apply (fr_apresent_grows _ (ms_mem ms3)); [exact HG4|].
                   exact (fr_apresent_grows _ mem3 (ms_mem ms3) a HG3 Ha).
                 - intros a Ha. apply Hpres5. lia. }
               assert (BAND6 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
                 aview segs (w_H W3) (ms_mem ms4) s = aview segs (w_H W) memc s).
               { intros s Hs. rewrite (UN5 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND1245 s Hs)|].
                 unfold ZS5. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
                 unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
               (* the registers at the second __toread call *)
               lreg HS0 (1%bv : bv 5) V1.
               lreg HS0 (2%bv : bv 5) V2.
               lreg HS0 (3%bv : bv 5) V3.
               lreg HS0 (4%bv : bv 5) V4.
               lreg HS0 (8%bv : bv 5) V8.
               lreg HS0 (10%bv : bv 5) V10.
               assert (Rra2 : getr (ms_regs ms4) 1%bv = Z_to_bv 64 (val A_TEXT + 168))
                 by (rewrite V1; exact (fr_codeptr_val val _ 168 HEIb)).
               assert (Hspc2 : spZ (ms_regs ms4) = spZ regs - 64).
               { change (spZ (ms_regs ms4)) with (bv_unsigned (getr (ms_regs ms4) 2%bv)). rewrite V2. cbn [sv_denot].
                 rewrite !ew_havoc_old by lia. rewrite U2sp. rewrite unsigned_lit_small by lia. lia. }
               assert (Rgp2 : getr (ms_regs ms4) 3%bv = w64 (as_gp B)).
               { rewrite V3. cbn [sv_denot]. rewrite !ew_havoc_old by lia. rewrite (Eimg_low val _ 3%nat ltac:(cbv [A_TEXT]; lia)),
                   (ew_Ereg_nat regs _ 3 3%bv eq_refl), Hgp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
               assert (Rtp2 : getr (ms_regs ms4) 4%bv = w64 (as_tp B)).
               { rewrite V4. cbn [sv_denot]. rewrite !ew_havoc_old by lia. rewrite (Eimg_low val _ 4%nat ltac:(cbv [A_TEXT]; lia)),
                   (ew_Ereg_nat regs _ 4 4%bv eq_refl), Htp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
               assert (Ra02 : getr (ms_regs ms4) 10%bv = w64 f).
               { rewrite V10. cbn [sv_denot]. rewrite !ew_havoc_old by lia. rewrite (Eimg_low val _ 13%nat ltac:(cbv [A_TEXT]; lia)),
                   (ew_Ereg_nat regs _ 13 13%bv eq_refl), G13. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
               assert (Rs0v2 : getr (ms_regs ms4) 8%bv = w64 f).
               { rewrite V8. cbn [sv_denot]. rewrite !ew_havoc_old by lia. rewrite (Eimg_low val _ 13%nat ltac:(cbv [A_TEXT]; lia)),
                   (ew_Ereg_nat regs _ 13 13%bv eq_refl), G13. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
               assert (Rs02 : s0Z (ms_regs ms4) = f)
                 by (unfold s0Z; rewrite Rs0v2; unfold w64; apply fa_u64_small; change SRC_FILE_BLOCK with 1304 in *; lia).
               assert (Hra_rng2 : 0 <= val A_TEXT + 168 < 2 ^ 64) by (destruct HBok as (_ & Hhi & _); lia).
               assert (Hra_ev2 : (val A_TEXT + 168) mod 2 = 0).
               { destruct HBok as (_ & _ & Hm4).
                 pose proof (Z_div_mod_eq_full (val A_TEXT) 4) as Hd. rewrite Hm4, Z.add_0_r in Hd.
                 rewrite Hd. replace (4 * (val A_TEXT / 4) + 168) with ((2 * (val A_TEXT / 4) + 84) * 2) by ring.
                 apply Z_mod_mult. }
               assert (Hret2 : YK0s.ret_ok (getr (ms_regs ms4) 1%bv)).
               { unfold YK0s.ret_ok. rewrite Rra2. unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by exact Hra_rng2.
                 rewrite Z.add_0_r. rewrite YK0s.land_m2_even by exact Hra_ev2. reflexivity. }
               assert (Hra40962 : 4096 <= val A_TEXT + 168 < 2 ^ 64)
                 by (split; [pose proof Hbase_lo; lia | exact (proj2 Hra_rng2)]).
               (* the second __toread call *)
               lazymatch type of HS0 with st_ok ?sg ?Ev ?ssx (restrict ?HH ?msr) =>
                 rewrite (st_ok_restrict_mkst sg HH Ev ssx msr HS0 ltac:(vm_compute; reflexivity));
                 replace (ss_pc ssx) with (sigma FS_toread) by (vm_compute; reflexivity) end.
               eapply SRr_bind.
               { apply (frd_call_toread segs B K LAWS segs_low (sigma FS_toread) HTOREAD
                        STK sp0 FP ly S W0 mem0 md0 own lyc Sc W3 (ms_mem ms4) _ k regs (ms_regs ms4) []
                        f b (p + rread_k nm (Z.of_nat (length C)) p) 24 (val A_TEXT + 168) C HJ Hspc2 Hal16 Hstk1 Hsple Rra2
                        Hret2 Hra40962 Rgp2 Rtp2
                        ltac:(apply achain_low; rewrite Rs02; change SRC_FILE_BLOCK with 1304 in *; lia)
                        Ra02 Hblkf Hblkb Hbstk Hunb5 Hfl5 HWRF). }
               intros W5 c5 Hle5 (ly5 & S5 & regs5 & mem5 & md5 & Hcfg5 & HJ5 & HJt5 & HPpres5 & Ht5post).
               subst c5. rewrite Rra2.
               destruct Ht5post as (-> & -> & Ha0t5 & Hunb6 & Hfl6 & Hmd6 & Hrp6 & Hre6 & Hband6). (* POS *)
               pose proof HJt5 as (_ & _ & _ & _ & Hiot5 & _ & _ & _ & G1t5 & _ & _ & _ & _ & _ & _ & _ & _).
               pose proof HJ5 as (HAR6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres6 & _ & _ & _).
               pose proof HJ as (HARc5 & _).
               assert (KST5 : forall a, spZ regs + -64 <= a < spZ regs + 0 ->
                 aview segs (w_H W5) mem5 a = aview segs (w_H W3) (ms_mem ms4) a).
               { intros a Ha. apply G1t5.
                 - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
                 - rewrite Hspc2. lia. }
               assert (KPR5 : forall a, spZ regs + -64 <= a < spZ regs + 0 -> apresent (w_H W5) mem5 a).
               { intros a Ha. apply Hpres6. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
               (* reseat at the return 0x8ef04 *)
               lazymatch type of HS0 with st_ok _ ?Ev ?ssc ?msc =>
                 let rs := eval vm_compute in (pick (ss_mem ssc) [0%nat]) in
                 assert (Hkept5 : Forall (region_kept segs Ev (ms_mem msc) (mrestrict (w_H W5) mem5)) rs)
                   by (cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
                       apply (frd_region_kept Ev W3 W5 (ms_mem ms4) mem5 2%nat (spZ regs)); [exact VB2b | exact KST5 | exact KPR5]);
                 pose proof (fr_after_call segs val 88%nat Ev ssc msc regs5 (mrestrict (w_H W5) mem5) rs 168
                   HEIb ltac:(lia) HS0 ltac:(vm_compute; reflexivity) ltac:(cbv; lia)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HPpres5 Hkept5) as HSd;
                 let ss5 := eval vm_compute in (ss_after_call ssc rs 88 168) in
                 change (ss_after_call ssc rs 88 168) with ss5 in HSd
               end.
               rewrite <- restrict_mkst_fx in HSd.
               clear HS0 Hkept5 V1 V2 V3 V4 V8 V10.
               pose proof (fr_img_env_havoc val _ 88 (map (getr regs5) CLOB) HEIb ltac:(rewrite length_map; cbv; lia)) as HEIc.
               pose proof (frd_base_havoc _ 88 (map (getr regs5) CLOB) 2 (spZ regs) ltac:(lia) VB2b) as VB2c.
               pose proof (frd_ew_havoc _ 88 (map (getr regs5) CLOB) 12 _ ltac:(lia) HE12b) as HE12c.
               pose proof (frd_ew_havoc _ 88 (map (getr regs5) CLOB) 11 _ ltac:(lia) HE11b) as HE11c.
               pose proof (frd_ew_havoc _ 88 (map (getr regs5) CLOB) 68 _ ltac:(lia) HE68) as HE68c.
               lazymatch type of HSd with st_ok_pi _ _ ?E4 _ _ =>
                 clear SHOK; assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E4 (mrestrict (w_H W5) mem5)) by apply Forall_nil end.
               rename HSd into HS0. clear HJ. rename HJ5 into HJ.
               (* 0x8ef04 bnez a0: __toread returned -1 (F_EOF) *)
               frd_branch_auto; clear HS0; intros Hc6 HS0.
               --- frd_run RUNF HS0 HJ SHOK.
                   { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
                     destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
                     rewrite ?VB2c in Hr0; apply AWRgen; lia. }
                   eapply (RETF W5 _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity)).
                   intros matR.
                   set (ZS6 := fun a => spZ regs - 64 <= a < spZ regs).
                   pose proof (fr_kept_of_frame segs _ _ (w_H W5) _ _ ZS6 HFr5
                     ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                           repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2c in Hrr; unfold ZS6; lia|]);
                           destruct Hin)) as UN6.
                   pose proof HJ as (_ & HlyL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & HstL & _ & _). (* POS *)
                   destruct HlyL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HsloL & HshiL & _). (* POS *)
                   pose proof HstL as (_ & _ & HcL & _ & _ & H47L & _). (* POS *)
                   assert (HceilL : alloc_ceiling <= ly_stk_lo lyc) by (rewrite HsloL; exact HcL).
                   assert (HhiL : ly_stk_hi lyc <= 2 ^ 64) by (rewrite HshiL; lia).
                   (* the return address, the callee-saved registers and the result k *)
                   frd_reg HS0 (1%bv : bv 5) R1x.
                   assert (R1 : getr (ms_regs ms5) 1 = getr regs 1).
                   { rewrite R1x. cbn [sv_denot]. rewrite !ew_havoc_old by lia.
                     rewrite (Eimg_low val _ 1%nat ltac:(cbv [A_TEXT]; lia)), (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r.
                     apply Z_to_bv_bv_unsigned. }
                   assert (HPR : aregs_preserved regs (ms_regs ms5)).
                   { lazymatch type of HS0 with st_ok_pi _ _ ?E ?ss _ =>
                       exact (aregs_preserved_of_st_ok segs (w_H W5) E (abs_ss val ss) ms5 regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]
                                HS0 (frd_ea_havoc2 _ _ 88 _ (frd_ea_havoc2 _ _ 64 _ (frd_ea_havoc val regs _ 40 _ ltac:(lia)) ltac:(lia))
                                       ltac:(lia))
                                ltac:(vm_compute; reflexivity)) end. }
                   frd_reg HS0 (10%bv : bv 5) R10x.
                   assert (R10 : getr (ms_regs ms5) 10 = w64 (rread_k nm (Z.of_nat (length C)) p)).
                   { rewrite R10x, denot_lit_U, (frd_U_retk _ nm _ HE12c HE11c HE68c Hnm ltac:(lia)). reflexivity. }
                   (* what __toread kept, and what the path kept *)
                   assert (K7 : rread_kept segs B RTOREAD_STK lyc Sc W3 (ms_mem ms4) W5 mem5 (spZ (ms_regs ms4))
                                  (fun a => f <= a < f + SRC_FILE_BLOCK)).
                   { apply (frd_kept_of_acall segs B).
                     apply (acall_kept_of_journal segs B segs_low RTOREAD_STK (spZ (ms_regs ms4)) (rtoread_fp f) [] lyc Sc W3
                              (ms_mem ms4) _ lyc Sc W5 mem5 md5 0 (fun a => f <= a < f + SRC_FILE_BLOCK) HJt5 HARc5);
                       [| | exact Hcl].
                     - intros a (r & Hr & Ha). unfold rtoread_fp in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact Ha.
                     - intros bb m i Hb _ _. exact Hb. }
                   assert (K67 : rread_kept segs B RFREAD_STK lyc Sc W memc W5 mem5 (spZ regs) (rread_wrset f d nm)).
                   { apply (frd_kept_trans segs B RFREAD_STK RTOREAD_STK RFREAD_STK lyc Sc W memc W3 (ms_mem ms4) W5 mem5
                              (spZ regs) (spZ (ms_regs ms4)) (spZ regs) (rread_wrset f d nm) (fun a => f <= a < f + SRC_FILE_BLOCK)
                              (rread_wrset f d nm) K6 K7).
                     - lia.
                     - lia.
                     - rewrite Hspc2. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK. lia.
                     - rewrite Hspc2. lia.
                     - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
                     - lia.
                     - intros a Ha. apply Hpres0. lia.
                     - intros a Ha. exact Ha.
                     - intros a Ha. left. exact Ha. }
                   assert (KF : rread_kept segs B RFREAD_STK lyc Sc W memc W5 (ms_mem ms5) (spZ regs) (rread_wrset f d nm)).
                   { apply (frd_kept_extend lyc Sc W memc W5 mem5 md5 (ms_mem ms5) (spZ regs) (rread_wrset f d nm) K67 HAR6).
                     - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
                     - lia.
                     - intros a Ha. apply Hpres0. lia.
                     - intros a Ha Hs. apply UN6; [exact Ha|]. unfold ZS6. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
                     - intros a Ha. exact (fr_apresent_grows _ mem5 (ms_mem ms5) a HG5 Ha).
                     - intros a Ha. apply HpresF. lia. }
                   (* the k bytes mread delivered: kept by the last run, by __toread and by the run before it *)
                   assert (DK : forall x, d <= x < d + nm -> aview segs (w_H W5) (ms_mem ms5) x = aview segs (w_H W3) mem3 x).
                   { intros x Hx.
                     pose proof (proj2 (Hdwr x Hx)) as Hxs.
                     assert (Hxr : 0 <= x < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hdam; lia).
                     transitivity (aview segs (w_H W5) mem5 x).
                     { apply UN6; [exact Hxr|]. unfold ZS6. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hxs. lia. }
                     transitivity (aview segs (w_H W3) (ms_mem ms4) x).
                     { apply (frd_dest_kept RTOREAD_STK lyc Sc W3 (ms_mem ms4) W5 mem5 (spZ (ms_regs ms4))
                                (fun a => f <= a < f + SRC_FILE_BLOCK) d nm K7 Hdat HceilL HhiL); [|exact Hx].
                       intros a Ha. pose proof (proj2 (Hdwr a Ha)) as Has. split.
                       - first [ (clear - Hdf Ha; cbv beta; change SRC_FILE_BLOCK with 1304 in *; lia) | (change SRC_FILE_BLOCK with 1304 in *; lia) ].
                       - rewrite Hspc2. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
                     apply UN5; [exact Hxr|]. unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hxs. lia. }
                   assert (HGA : garr8 segs (rd W5 (ms_mem ms5)) d
                             (firstn (Z.to_nat (rread_k nm (Z.of_nat (length C)) p)) (skipn (Z.to_nat p) C))).
                   { apply (garr8_frame segs (rd W3 mem3) (rd W5 (ms_mem ms5)) d _ Hgarrm).
                     intros x Hx. rewrite length_firstn, length_skipn in Hx. apply (mbyte_of_aview segs). apply DK. lia. }
                   (* the stream after __toread, the orientation word and the band *)
                   assert (FA6 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W5 (ms_mem ms5)) a = mbyte segs (rd W5 mem5) a).
                   { intros a Ha. apply (mbyte_of_aview segs). apply UN6; [change SRC_FILE_BLOCK with 1304 in *; lia|].
                     unfold ZS6. change SRC_FILE_BLOCK with 1304 in *. lia. }
                   assert (BA6 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W5 (ms_mem ms5)) a = mbyte segs (rd W5 mem5) a).
                   { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
                     pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
                     intros a Ha. apply (mbyte_of_aview segs). apply UN6; [lia|]. unfold ZS6.
                     unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
                   assert (EA6 : forall a, asrc_env_addr K a -> mbyte segs (rd W5 (ms_mem ms5)) a = mbyte segs (rd W5 mem5) a).
                   { intros a Ha. apply (mbyte_of_aview segs).
                     pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
                     pose proof (segs_low a Hi) as Hl. apply UN6; [unfold kLowMemEnd in Hl; lia|]. unfold ZS6.
                     unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
                   assert (OA6 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W5 (ms_mem ms5)) a = mbyte segs (rd W5 mem5) a).
                   { intros a Ha. apply (mbyte_of_aview segs).
                     pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
                     pose proof (segs_low a Hi) as Hl. apply UN6; [unfold kLowMemEnd in Hl; lia|]. unfold ZS6.
                     unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
                   assert (HAT : asource_at segs K (rd W5 (ms_mem ms5)) f b C (p + rread_k nm (Z.of_nat (length C)) p))
                     by exact (asource_at_frame segs K (rd W5 mem5) (rd W5 (ms_mem ms5)) f b C _ FA6 BA6 EA6 OA6 (proj1 Hunb6)).
                   assert (HMD6 : source_mode segs (rd W5 (ms_mem ms5)) f U32M1).
                   { apply (source_mode_frame segs (rd W5 mem5) (rd W5 (ms_mem ms5)) f U32M1); [|exact Hmd6].
                     intros a Ha. apply FA6. change SRC_FILE_BLOCK with 1304 in *. lia. }
                   assert (BAND7 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
                     aview segs (w_H W5) mem5 s = aview segs (w_H W) memc s)
                     by (intros s Hs; rewrite (Hband6 s Hs); exact (BAND6 s Hs)).
                   destruct (aos_step_closed _ _ _ Hcl Hiot5) as (Hfd6 & Hfs6 & _ & _).
                   assert (Hfds6 : m_fds md5 = m_fds mdc) by (unfold m_fds in *; rewrite Hfd6; exact Hfds3).
                   assert (Hfss6 : m_fs md5 = m_fs mdc) by (unfold m_fs in *; rewrite Hfs6; exact Hfss3).
                   unfold rread_post_base.
                   eexists lyc, Sc, (ms_regs ms5), (ms_mem ms5), _.
                   split; [rewrite R1, (fr_ret_of_ok _ Hra); reflexivity|].
                   split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ|].
                   split; [exact HPR|].
                   split; [exact KF|].
                   unfold rfread_post. cbv zeta.
                   split; [reflexivity|]. split; [reflexivity|].
                   split; [exact R10|].
                   split; [exact HGA|].
                   split; [exact HAT|].
                   split; [exact HMD6|].
                   split; [intros Hz; exfalso; exact (Hnm1 Hz)|].
                   split; [exact Hfds6|]. split; [exact Hfss6|].
                   intros s Hs. rewrite (UN6 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND7 s Hs)|].
                   unfold ZS6. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
                   unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
               --- exfalso. cbn [branch_taken sv_denot havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB] in Hc6.
                   rewrite Ha0t5 in Hc6. vm_compute in Hc6. discriminate.
            ** (* s4 = 0: k = nm; return nm (0x8ef2c-0x8ef34 with s1 = 1) *)
               lazymatch type of HE12b with ew ?E3 _ = _ =>
                 assert (HE68 : ew E3 68 = w64 (rread_k nm (Z.of_nat (length C)) p))
                   by (cbn [havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB]; exact Ha0m) end.
               assert (Hjn : rread_k nm (Z.of_nat (length C)) p = nm).
               { pose proof Hc5 as Hcp. rewrite !denot_lit_U in Hcp.
                 rewrite (frd_U_s4k _ nm _ HE12b HE11b HE68 Hnm ltac:(lia)), U_SLit in Hcp.
                 rewrite (zcanon_id 0) in Hcp by (unfold M64; lia).
                 cbn [branch_taken] in Hcp. apply Bool.negb_false_iff in Hcp. apply bv_eqb_eq in Hcp.
                 apply (f_equal bv_unsigned) in Hcp. rewrite !unsigned_lit_small in Hcp by lia. lia. }
               frd_run RUNF HS0 HJ SHOK.
               { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
                 destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
                 rewrite ?VB2b in Hr0; apply AWRgen; lia. }
               eapply (RETF W3 _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity)).
               intros matR.
               set (ZS5 := fun a => spZ regs - 64 <= a < spZ regs).
               pose proof (fr_kept_of_frame segs _ _ (w_H W3) _ _ ZS5 HFr3
                 ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                       repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2b in Hrr; unfold ZS5; lia|]);
                       destruct Hin)) as U5.
               pose proof (fr_kept_of_frame segs _ _ (w_H W3) _ _ ZS5 HFr4
                 ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                       repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2b in Hrr; unfold ZS5; lia|]);
                       destruct Hin)) as U6.
               assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ ZS5 a -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a)
                 by (intros a Ha Hz; rewrite (U6 a Ha Hz), (U5 a Ha Hz); reflexivity).
               clear U5 U6.
               pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & _ & _ & _).
               frd_reg HS0 (1%bv : bv 5) R1x.
               assert (R1 : getr (ms_regs ms4) 1 = getr regs 1).
               { rewrite R1x. cbn [sv_denot]. rewrite !ew_havoc_old by lia.
                 rewrite (Eimg_low val _ 1%nat ltac:(cbv [A_TEXT]; lia)), (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r.
                 apply Z_to_bv_bv_unsigned. }
               assert (HPR : aregs_preserved regs (ms_regs ms4)).
               { lazymatch type of HS0 with st_ok_pi _ _ ?E ?ss _ =>
                   exact (aregs_preserved_of_st_ok segs (w_H W3) E (abs_ss val ss) ms4 regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]
                            HS0 (frd_ea_havoc2 _ _ 64 _ (frd_ea_havoc val regs _ 40 _ ltac:(lia)) ltac:(lia))
                            ltac:(vm_compute; reflexivity)) end. }
               frd_reg HS0 (10%bv : bv 5) R10x.
               assert (R10 : getr (ms_regs ms4) 10 = w64 nm).
               { rewrite R10x. cbn [sv_denot]. rewrite HE12b. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
               assert (FA5 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W3 (ms_mem ms4)) a = mbyte segs (rd W3 mem3) a).
               { intros a Ha. apply (mbyte_of_aview segs). apply UN5; [change SRC_FILE_BLOCK with 1304 in *; lia|].
                 unfold ZS5. change SRC_FILE_BLOCK with 1304 in *. lia. }
               assert (BA5 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W3 (ms_mem ms4)) a = mbyte segs (rd W3 mem3) a).
               { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
                 pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
                 intros a Ha. apply (mbyte_of_aview segs). apply UN5; [lia|]. unfold ZS5.
                 unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
               assert (EA5 : forall a, asrc_env_addr K a -> mbyte segs (rd W3 (ms_mem ms4)) a = mbyte segs (rd W3 mem3) a).
               { intros a Ha. apply (mbyte_of_aview segs).
                 pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
                 pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
                 unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
               assert (OA5 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W3 (ms_mem ms4)) a = mbyte segs (rd W3 mem3) a).
               { intros a Ha. apply (mbyte_of_aview segs).
                 pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
                 pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
                 unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
               assert (HAT : asource_at segs K (rd W3 (ms_mem ms4)) f b C (p + rread_k nm (Z.of_nat (length C)) p))
                 by exact (asource_at_frame segs K (rd W3 mem3) (rd W3 (ms_mem ms4)) f b C _ FA5 BA5 EA5 OA5 Hatm).
               assert (HMD5 : source_mode segs (rd W3 (ms_mem ms4)) f U32M1).
               { apply (source_mode_frame segs (rd W3 mem3) (rd W3 (ms_mem ms4)) f U32M1); [|exact Hmdm3].
                 intros a Ha. apply FA5. change SRC_FILE_BLOCK with 1304 in *. lia. }
               assert (HGA : garr8 segs (rd W3 (ms_mem ms4)) d
                         (firstn (Z.to_nat (rread_k nm (Z.of_nat (length C)) p)) (skipn (Z.to_nat p) C))).
               { apply (garr8_frame segs (rd W3 mem3) (rd W3 (ms_mem ms4)) d _ Hgarrm).
                 intros x Hx. rewrite length_firstn, length_skipn in Hx. apply (mbyte_of_aview segs). apply UN5.
                 - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hdam. lia.
                 - unfold ZS5. intros Hz. apply (proj2 (Hdwr x ltac:(lia))).
                   unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK. lia. }
               assert (KF : rread_kept segs B RFREAD_STK lyc Sc W memc W3 (ms_mem ms4) (spZ regs) (rread_wrset f d nm)).
               { apply (frd_kept_extend lyc Sc W memc W3 mem3 md3 (ms_mem ms4) (spZ regs) (rread_wrset f d nm) K1245 HAR3).
                 - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
                 - lia.
                 - intros a Ha. apply Hpres0. lia.
                 - intros a Ha Hs. apply UN5; [exact Ha|]. unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
                 - intros a Ha. apply (fr_apresent_grows _ (ms_mem ms3)); [exact HG4|].
                   exact (fr_apresent_grows _ mem3 (ms_mem ms3) a HG3 Ha).
                 - intros a Ha. apply HpresF. lia. }
               unfold rread_post_base.
               eexists lyc, Sc, (ms_regs ms4), (ms_mem ms4), _.
               split; [rewrite R1, (fr_ret_of_ok _ Hra); reflexivity|].
               split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ|].
               split; [exact HPR|].
               split; [exact KF|].
               unfold rfread_post. cbv zeta.
               split; [reflexivity|]. split; [reflexivity|].
               split; [rewrite Hjn; exact R10|].
               split; [exact HGA|].
               split; [exact HAT|].
               split; [exact HMD5|].
               split; [intros Hz; exfalso; exact (Hnm1 Hz)|].
               split; [exact Hfds3|]. split; [exact Hfss3|].
               intros s Hs. rewrite (UN5 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND1245 s Hs)|].
               unfold ZS5. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
               unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
    * (* fl = 24: __toread returned -1, return (s6 - s4) / s1 *)
      frd_branch_auto; clear HS0; intros Hc3 HS0.
      -- frd_run RUNF HS0 HJ SHOK.
         { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
           destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
           rewrite ?VB2a, ?VB13a in Hr0; [lia | apply AWRgen; lia]. }
         eapply (RETF W2 _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity)).
         intros matR.
         (* the last run wrote only fread's frame *)
         set (ZS4 := fun a => spZ regs - 64 <= a < spZ regs).
         pose proof (fr_kept_of_frame segs _ _ (w_H W2) _ _ ZS4 HFr2
           ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                 repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2a, ?VB13a in Hrr; unfold ZS4; lia|]);
                 destruct Hin)) as UN4.
         pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & _ & _ & _).
         (* the return address, the callee-saved registers and the result 0 *)
         frd_reg HS0 (1%bv : bv 5) R1x.
         assert (R1 : getr (ms_regs ms2) 1 = getr regs 1).
         { rewrite R1x. cbn [sv_denot]. rewrite ew_havoc_old by lia.
           rewrite (Eimg_low val _ 1%nat ltac:(cbv [A_TEXT]; lia)), (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r.
           apply Z_to_bv_bv_unsigned. }
         assert (HPR : aregs_preserved regs (ms_regs ms2)).
         { lazymatch type of HS0 with st_ok_pi _ _ ?E ?ss _ =>
             exact (aregs_preserved_of_st_ok segs (w_H W2) E (abs_ss val ss) ms2 regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]
                      HS0 (frd_ea_havoc val regs _ 40 _ ltac:(lia)) ltac:(vm_compute; reflexivity)) end. }
         frd_reg HS0 (10%bv : bv 5) R10x.
         assert (R10 : getr (ms_regs ms2) 10 = w64 0).
         { rewrite R10x, denot_lit_U, (frd_U_ret0 _ nm HE12a HE11a Hnm). reflexivity. }
         (* the stream, the orientation word and what the path kept *)
         assert (FA4 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W2 (ms_mem ms2)) a = mbyte segs (rd W2 mem2) a).
         { intros a Ha. apply (mbyte_of_aview segs). apply UN4; [change SRC_FILE_BLOCK with 1304 in *; lia|].
           unfold ZS4. change SRC_FILE_BLOCK with 1304 in *. lia. }
         assert (BA4 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W2 (ms_mem ms2)) a = mbyte segs (rd W2 mem2) a).
         { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
           pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
           intros a Ha. apply (mbyte_of_aview segs). apply UN4; [lia|]. unfold ZS4.
           unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
         assert (EA4 : forall a, asrc_env_addr K a -> mbyte segs (rd W2 (ms_mem ms2)) a = mbyte segs (rd W2 mem2) a).
         { intros a Ha. apply (mbyte_of_aview segs).
           pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
           pose proof (segs_low a Hi) as Hl. apply UN4; [unfold kLowMemEnd in Hl; lia|]. unfold ZS4.
           unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
         assert (OA4 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W2 (ms_mem ms2)) a = mbyte segs (rd W2 mem2) a).
         { intros a Ha. apply (mbyte_of_aview segs).
           pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
           pose proof (segs_low a Hi) as Hl. apply UN4; [unfold kLowMemEnd in Hl; lia|]. unfold ZS4.
           unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
         assert (HAT : asource_at segs K (rd W2 (ms_mem ms2)) f b C p)
           by exact (asource_at_frame segs K (rd W2 mem2) (rd W2 (ms_mem ms2)) f b C p FA4 BA4 EA4 OA4 (proj1 Hunb2)).
         assert (HMD4 : source_mode segs (rd W2 (ms_mem ms2)) f U32M1).
         { apply (source_mode_frame segs (rd W2 mem2) (rd W2 (ms_mem ms2)) f U32M1); [|exact Hmd2].
           intros a Ha. apply FA4. change SRC_FILE_BLOCK with 1304 in *. lia. }
         assert (KF : rread_kept segs B RFREAD_STK lyc Sc W memc W2 (ms_mem ms2) (spZ regs) (rread_wrset f d nm)).
         { apply (frd_kept_extend lyc Sc W memc W2 mem2 md2 (ms_mem ms2) (spZ regs) (rread_wrset f d nm) K12 HAR2).
           - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
           - lia.
           - intros a Ha. apply Hpres0. lia.
           - intros a Ha Hs. apply UN4; [exact Ha|]. unfold ZS4. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
           - intros a Ha. exact (fr_apresent_grows _ mem2 (ms_mem ms2) a HG2 Ha).
           - intros a Ha. apply HpresF. lia. }
         assert (Rk0 : rread_k nm (Z.of_nat (length C)) p = 0)
           by (pose proof (HEOF eq_refl) as Hpn; unfold rread_k; lia).
         unfold rread_post_base.
         eexists lyc, Sc, (ms_regs ms2), (ms_mem ms2), _.
         split; [rewrite R1, (fr_ret_of_ok _ Hra); reflexivity|].
         split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ|].
         split; [exact HPR|].
         split; [exact KF|].
         unfold rfread_post. cbv zeta. rewrite Rk0.
         split; [reflexivity|]. split; [reflexivity|].
         split; [exact R10|].
         split; [apply frd_garr8_firstn_nil|].
         split; [rewrite Z.add_0_r; exact HAT|].
         split; [exact HMD4|].
         split; [intros Hz; exfalso; exact (Hnm1 Hz)|].
         split; [exact Hfds2|]. split; [exact Hfss2|].
         intros s Hs. rewrite (UN4 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND12 s Hs)|].
         unfold ZS4. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
         unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
      -- exfalso. cbn [branch_taken sv_denot havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB] in Hc3.
         rewrite Ha0t in Hc3. vm_compute in Hc3. discriminate.
  + (* nm = 0: no call; the walk runs to the return *)
    frd_run RUNF HS0 HJ SHOK.
    { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
      rewrite ?VB2, ?VB13 in Hr0; apply AWRgen; lia. }
    eapply (RETF W _ _ _ _ _ HS0 eq_refl); [vm_compute; reflexivity|].
    intros matR.
    set (ZS := fun a => (spZ regs - 64 <= a < spZ regs) \/ (f + 8 <= a < f + 16) \/ (f + 136 <= a < f + 140)).
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr
      ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZS; lia|]);
            destruct Hin)) as U0.
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr0
      ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZS; lia|]);
            destruct Hin)) as U1.
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr1
      ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZS; lia|]);
            destruct Hin)) as U2.
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ZS a -> aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Ha Hz. rewrite (U2 a Ha Hz), (U1 a Ha Hz), (U0 a Ha Hz). reflexivity. }
    clear U0 U1 U2.
    (* the return address and the callee-saved registers *)
    frd_reg HS0 (1%bv : bv 5) R1x.
    assert (R1 : getr (ms_regs ms1) 1 = getr regs 1).
    { rewrite R1x. cbn [sv_denot]. rewrite (Eimg_low val _ 1%nat ltac:(cbv [A_TEXT]; lia)).
      rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
    assert (HPR : aregs_preserved regs (ms_regs ms1)).
    { lazymatch type of HS0 with st_ok_pi _ _ ?E ?ss _ =>
        exact (aregs_preserved_of_st_ok segs (w_H W) E (abs_ss val ss) ms1 regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]
                 HS0 (fr_env_agree val regs _) ltac:(vm_compute; reflexivity)) end. }
    unfold rread_post_base.
    eexists lyc, Sc, (ms_regs ms1), (ms_mem ms1), _.
    split; [rewrite R1, (fr_ret_of_ok _ Hra); reflexivity|].
    split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ|].
    split; [exact HPR|].
    (* the two branch facts on this leaf: the window is empty and nm = 0 *)
    assert (Hw0 : Z.of_nat (length Wl) = 0).
    { pose proof Hc as Hcp. cbn [branch_taken sv_denot] in Hcp. rewrite HE32, HE33 in Hcp.
      unfold w64 in Hcp. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in Hcp.
      apply bv_eqb_eq in Hcp. apply (f_equal bv_unsigned) in Hcp.
      rewrite !unsigned_lit_small in Hcp by lia. lia. }
    assert (Hnm0 : nm = 0).
    { pose proof Hc2 as Hcp. cbn [branch_taken sv_denot] in Hcp. rewrite HE12, HE11 in Hcp.
      unfold w64 in Hcp. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in Hcp.
      apply Bool.negb_false_iff in Hcp. apply bv_eqb_eq in Hcp. rewrite m_mul, v_mul_one in Hcp by lia.
      apply (f_equal bv_unsigned) in Hcp. rewrite !unsigned_lit_small in Hcp by lia. exact Hcp. }
    subst nm.
    (* the final FILE cells, read off the final symbolic state *)
    lazymatch type of HS0 with st_ok_pi _ _ ?E ?ss ?ms =>
      pose proof (st_ok_mem_ok segs E (abs_ss val ss) ms HS0) as (_ & HRS & _) end.
    cbn [ss_mem abs_ss setpc ms_mem restrict] in HRS.
    pose proof (Forall_inv (Forall_inv_tail HRS)) as HR1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HRS))) as HR2.
    destruct HR1 as (_ & _ & _ & HC1). destruct HR2 as (_ & _ & _ & HC2c).
    cbn [YP09.r_base YP09.r_chunks] in HC1, HC2c. rewrite VB13 in HC1, HC2c.
    pose proof (Forall_inv HC1) as CK8.
    pose proof (Forall_inv (Forall_inv_tail HC1)) as CK16.
    pose proof (Forall_inv HC2c) as CK136.
    assert (N8 : val_mem segs (rd W (ms_mem ms1)) (f + 8) 8 rp).
    { apply (val_of_chunk_ok segs _ _ _ 8 8%N (SOff 32 0) rp CK8);
      [cbn [sv_denot]; rewrite HE32; unfold w64; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
    assert (N16 : val_mem segs (rd W (ms_mem ms1)) (f + 16) 8 re).
    { apply (val_of_chunk_ok segs _ _ _ 16 8%N (SOff 33 0) re CK16);
      [cbn [sv_denot]; rewrite HE33; unfold w64; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
    assert (N136 : val_mem segs (rd W (ms_mem ms1)) (f + 136) 4 U32M1).
    { apply (frd_chunk_val4 _ _ _ _ _ CK136). intros i Hi.
      cbn [sv_denot]. rewrite HE35.
      destruct Hmdcase as [-> | ->]; unfold U32M1;
      (assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia);
      destruct Hi' as [-> | [-> | [-> | ->]]]; apply bv_eq; vm_compute; reflexivity. }
    assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RFREAD_STK <= a < spZ regs) -> ~ rread_wrset f d 0 a ->
      aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Ha Hw Hwr. apply UN; [exact Ha|]. unfold ZS. intros Hz. unfold rread_wrset in Hwr.
      change SRC_FILE_BLOCK with 1304 in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hw. lia. }
    assert (AGimg : forall a, in_img segs a -> aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Hi. pose proof (segs_low a Hi) as Hlo. apply UN; [unfold kLowMemEnd in Hlo; lia|].
      unfold ZS. intros Hz. destruct Hz as [Hz | Hz]; [unfold kLowMemEnd in Hlo; lia|].
      apply (blk_img segs B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK a HAR Hblkf); [|exact Hi].
      rewrite RQ. change SRC_FILE_BLOCK with 1304 in *. lia. }
    assert (APG : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a).
    { intros a Ha. apply (fr_apresent_grows _ (ms_mem ms0)); [exact HG1|].
      apply (fr_apresent_grows _ (ms_mem ms)); [exact HG0|].
      apply (fr_apresent_grows _ memc); [exact HG|exact Ha]. }
    assert (APW : forall a, spZ regs - RFREAD_STK <= a < spZ regs -> apresent (w_H W) (ms_mem ms1) a).
    { intros a Ha. apply APG. apply Hpres0. lia. }
    split.
    { eapply frd_kept_of_agree_all;
      [exact LAWS | exact HAR | unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia
      | exact AG | exact AGimg | exact APG | exact APW]. }
    (* the FILE in the new memory: everything but the orientation word is as it was *)
    assert (FAv : forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) ->
      aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Ha Hn. destruct (Z_lt_le_dec a (f + 16)) as [Hl | Hl]; [destruct (Z_lt_le_dec a (f + 8)) as [Hl2 | Hl2]|].
      - apply UN; [change SRC_FILE_BLOCK with 1304 in *; lia|]. unfold ZS. change SRC_FILE_BLOCK with 1304 in *. lia.
      - apply (fr_val_mem_aview_eq (w_H W) memc (ms_mem ms1) (f + 8) 8 rp M8 N8). cbn. lia.
      - apply UN; [change SRC_FILE_BLOCK with 1304 in *; lia|]. unfold ZS. change SRC_FILE_BLOCK with 1304 in *. lia. }
    assert (FA : forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) ->
      mbyte segs (rd W (ms_mem ms1)) a = mbyte segs (rd W memc) a).
    { intros a Ha Hn. apply (mbyte_of_aview segs). apply FAv; assumption. }
    assert (BA : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W (ms_mem ms1)) a = mbyte segs (rd W memc) a).
    { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
      pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
      intros a Ha. apply (mbyte_of_aview segs). apply UN; [lia|]. unfold ZS.
      change SRC_FILE_BLOCK with 1304 in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
    assert (EA : forall a, asrc_env_addr K a -> mbyte segs (rd W (ms_mem ms1)) a = mbyte segs (rd W memc) a).
    { intros a Ha. apply (mbyte_of_aview segs). apply AGimg.
      apply (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))). }
    assert (OA : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W (ms_mem ms1)) a = mbyte segs (rd W memc) a).
    { intros a Ha. apply (mbyte_of_aview segs). apply AGimg.
      apply (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))). }
    assert (HAW : asource_at_w segs K (rd W memc) f b C p Wl).
    { exists cpos, fl, mdv. cbv zeta.
      exact (conj Hp0 (conj Hpc (conj Hcn (conj Hnlt (conj Hbw (conj Hcpos (conj HWl (conj Hbok (conj Hgarr (conj HST
        (conj HWIN (conj HFL (conj HEOF (conj HMD (conj HCK (conj HENV (conj HOFL Hfnz))))))))))))))))). }
    assert (Rk0 : rread_k 0 (Z.of_nat (length C)) p = 0) by (unfold rread_k; lia).
    unfold rfread_post. cbv zeta. rewrite Rk0.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { frd_reg HS0 (10%bv : bv 5) R10x. rewrite R10x. cbn [sv_denot].
      rewrite (Eimg_low val _ 12%nat ltac:(cbv [A_TEXT]; lia)), (ew_Ereg_nat regs _ 12 12%bv eq_refl), G12.
      unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    split; [apply frd_garr8_firstn_nil|].
    split.
    { replace (p + 0) with (p + 0) by reflexivity.
      apply (asource_at_drain segs K (rd W memc) (rd W (ms_mem ms1)) f b C p Wl 0 U32M1 HAW).
      - lia.
      - cbn [skipn Z.to_nat]. apply (source_window_frame_mode segs (rd W memc) (rd W (ms_mem ms1)) f Wl FA HWIN).
      - intros a Ha H1 H2. apply FA; [exact Ha | exact H2].
      - split; [exact N136 | right; reflexivity].
      - exact BA.
      - exact EA.
      - exact OA. }
    split; [split; [exact N136 | right; reflexivity]|].
    split; [intros _ a Ha Hn; apply FAv; assumption|].
    split; [reflexivity|]. split; [reflexivity|].
    eapply frd_band_of_agree with (sp := spZ regs) (RSTK := RFREAD_STK) (f := f) (d := d) (l := 0);
      [exact LAWS | exact HAR | exact Hblkf | unfold amem_range in *; lia
      | unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia | exact AG].
- (* B: the window is not empty *)
  frd_run RUNF HS0 HJ SHOK.
  { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
    rewrite ?VB2, ?VB13 in Hr0; apply AWRgen; lia. }
  frd_branch_auto; clear HS0; intros Hc2 HS0.
  + (* B-short: the window is shorter than the request (bltu taken): copy the window, then the loop *)
    frd_run RUNF HS0 HJ SHOK.
    { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
      rewrite ?VB2, ?VB13 in Hr0; apply AWRgen; lia. }
    (* ===== Stage 1: the window-copy memcpy ===== *)
    repeat rewrite wvb_collapse in HJ.
    set (MOD := with_vm_backing (m_vm_lazy mdc) mat1 mdc) in *.
    set (E := EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) in *.
    assert (HE2 : ew E 2 = getr regs 2).
    { unfold E. rewrite (Eimg_low val _ 2%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_nat regs _ 2 2%bv eq_refl). }
    assert (HE3 : ew E 3 = getr regs 3).
    { unfold E. rewrite (Eimg_low val _ 3%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_nat regs _ 3 3%bv eq_refl). }
    assert (HE4 : ew E 4 = getr regs 4).
    { unfold E. rewrite (Eimg_low val _ 4%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_nat regs _ 4 4%bv eq_refl). }
    assert (HE10 : ew E 10 = w64 d).
    { unfold E. rewrite (Eimg_low val _ 10%nat ltac:(cbv [A_TEXT]; lia)). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact G10. }
    assert (Hrpre : rp <= re) by lia.
    assert (Hwin_eq : sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0))
                      = w64 (Z.of_nat (length Wl))).
    { cbn [sv_denot]. rewrite HE32, HE33. unfold w64. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
      rewrite (frd_win_val rp re (-1)) by first [lia | (vm_compute; reflexivity)].
      f_equal. lia. }
    assert (Htot_eq : sv_denot E (SMd M_MUL (SOff 12 0) (SOff 11 0)) = w64 nm).
    { cbn [sv_denot]. rewrite HE11, HE12. unfold w64. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
      rewrite m_mul. apply v_mul_one. lia. }
    assert (HWlpos : 0 < Z.of_nat (length Wl)).
    { assert (Hne : rp <> re).
      { intros Heq. pose proof Hc as Hcp. cbn [branch_taken sv_denot] in Hcp. rewrite HE32, HE33 in Hcp.
        unfold w64 in Hcp. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in Hcp.
        rewrite Heq, bv_eqb_refl in Hcp. discriminate. }
      lia. }
    assert (HWllt : Z.of_nat (length Wl) < nm).
    { pose proof Hc2 as Hcp. rewrite Hwin_eq, Htot_eq in Hcp.
      cbn [branch_taken] in Hcp. rewrite bv_ltu_unsigned in Hcp. apply Z.ltb_lt in Hcp.
      unfold w64 in Hcp. rewrite !unsigned_lit_small in Hcp by lia. exact Hcp. }
    (* register values at the memcpy call *)
    frd_reg0 HS0 (1%bv : bv 5) R1x.
    frd_reg0 HS0 (2%bv : bv 5) R2x.
    frd_reg0 HS0 (3%bv : bv 5) R3x.
    frd_reg0 HS0 (4%bv : bv 5) R4x.
    frd_reg0 HS0 (10%bv : bv 5) R10x.
    frd_reg0 HS0 (11%bv : bv 5) R11x.
    frd_reg0 HS0 (12%bv : bv 5) R12x.
    assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + 136)).
    { rewrite R1x. change (SOff 240 136) with (SOff A_TEXT 136). exact (fr_codeptr_val val E 136 ltac:(assumption)). }
    assert (Hspc : spZ (ms_regs ms1) = spZ regs - 64).
    { unfold spZ in *. rewrite R2x. cbn [sv_denot]. rewrite HE2.
      rewrite unsigned_lit_small by lia. lia. }
    assert (R3 : getr (ms_regs ms1) 3 = w64 (as_gp B)).
    { rewrite R3x. cbn [sv_denot]. rewrite HE3, Hgp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (R4 : getr (ms_regs ms1) 4 = w64 (as_tp B)).
    { rewrite R4x. cbn [sv_denot]. rewrite HE4, Htp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (R10 : getr (ms_regs ms1) 10 = w64 d).
    { rewrite R10x. cbn [sv_denot]. rewrite HE10. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (R11 : getr (ms_regs ms1) 11 = w64 rp).
    { rewrite R11x. cbn [sv_denot]. rewrite HE32. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (R12 : getr (ms_regs ms1) 12 = w64 (Z.of_nat (length Wl))).
    { rewrite R12x. cbn [sv_denot]. rewrite HE32, HE33. unfold w64. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
      rewrite (frd_win_val rp re 18446744073709551615) by first [lia | (vm_compute; reflexivity)].
      f_equal. lia. }
    clear R1x R2x R3x R4x R10x R11x R12x.
    (* the shadow band is unchanged from memc to ms_mem ms1 (prologue + orientation word only) *)
    assert (Hac2 : alloc_ceiling + RFREAD_STK <= spZ regs).
    { unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
    set (ZS := fun a => (spZ regs - 64 <= a < spZ regs) \/ (f + 8 <= a < f + 16) \/ (f + 136 <= a < f + 140)).
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr
      ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZS; lia|]);
            destruct Hin)) as U0.
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr0
      ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZS; lia|]);
            destruct Hin)) as U1.
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr1
      ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZS; lia|]);
            destruct Hin)) as U2.
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ZS a -> aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Ha Hz. rewrite (U2 a Ha Hz), (U1 a Ha Hz), (U0 a Ha Hz). reflexivity. }
    clear U0 U1 U2.
    assert (Hband : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) (ms_mem ms1) s = aview segs (w_H W) memc s).
    { intros s Hs.
      assert (HnZ : ~ ZS s).
      { unfold ZS. intros HZ.
        change SRC_FILE_BLOCK with 1304 in Hfapp. unfold in_app in Hfapp.
        unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hac2.
        unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *.
        destruct Hfapp as (Hf0' & [Hlo | [Hhi1 Hhi2]]); destruct HZ as [Hz | [Hz | Hz]]; lia. }
      apply (UN s); [unfold kLowMemEnd, kHighShadowEnd in Hs |- *; lia | exact HnZ]. }
    (* fread's destination, transported to the memory at the memcpy call *)
    assert (Hdest0 : rread_dest segs B STK sp0 FP ly S own lyc Sc W memc RFREAD_STK (spZ regs) d nm f b (Z.of_nat (length C))).
    { unfold rread_dest. split; [exact Hdf|]. split; [exact Hdb|]. split; [exact Hd0|]. split; [exact Hdam|].
      split; [exact Hdat|]. split; [exact Hdwr|]. split; [exact Hdra | exact Hdhull]. }
    assert (Hdest1 : rread_dest segs B STK sp0 FP ly S own lyc Sc W (ms_mem ms1) RFREAD_STK (spZ regs) d nm f b (Z.of_nat (length C))).
    { apply (frd_dest_sub segs B STK sp0 FP ly S own lyc Sc W memc W (ms_mem ms1)
        RFREAD_STK (spZ regs) RFREAD_STK (spZ regs) d nm d nm f b (Z.of_nat (length C)) Hdest0);
      [lia | lia | lia | lia | lia | exact Hband]. }
    (* the window bytes live in the FILE block *)
    assert (HWne : Wl <> []).
    { intros HW. rewrite HW in HWlpos. cbn [length] in HWlpos. lia. }
    destruct (Hgw HWne) as (Hrplo & Hgarrw).
    assert (Hra_rng : 0 <= val A_TEXT + 136 < 2 ^ 64) by (destruct HBok as (HB0 & HB1 & _); lia).
    assert (Hra_ev : (val A_TEXT + 136) mod 2 = 0).
    { destruct HBok as (_ & _ & Hm4).
      pose proof (Z_div_mod_eq_full (val A_TEXT) 4) as Hd. rewrite Hm4, Z.add_0_r in Hd.
      rewrite Hd. replace (4 * (val A_TEXT / 4) + 136) with ((2 * (val A_TEXT / 4) + 68) * 2) by ring.
      apply Z_mod_mult. }
    assert (Hret_mc : YK0s.ret_ok (getr (ms_regs ms1) 1%bv)).
    { unfold YK0s.ret_ok. rewrite R1. unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by exact Hra_rng.
      rewrite Z.add_0_r. rewrite YK0s.land_m2_even by exact Hra_ev. reflexivity. }
    (* the call *)
    rewrite (st_ok_restrict_mkst segs (w_H W) E _ ms1 HS0 ltac:(reflexivity)).
    cbn [ss_pc setpc].
    eapply SRr_bind.
    { eapply (frd_call_memcpy_file segs B LAWS segs_low (sigma FS_memcpy) HMEMCPY
        STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) MOD k regs (ms_regs ms1)
        d nm f b (Z.of_nat (length C)) d rp (Z.of_nat (length Wl))).
      - exact HJ.
      - exact Hspc.
      - exact Hal16.
      - exact Hstk1.
      - exact Hsple.
      - exact Hret_mc.
      - exact R3.
      - exact R4.
      - exact R10.
      - exact R11.
      - exact R12.
      - split; [lia | lia].
      - exact Hdest1.
      - lia.
      - lia.
      - exact Hblkf.
      - change SRC_BUF_OFF with 280 in Hrplo. lia.
      - change SRC_FILE_BLOCK with 1304 in *. lia. }
    intros W' c' Hle Hpost.
    destruct Hpost as (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR2 & H10_2 & Hcopy2 & Hkeep2 & Hbandm & Hpres2 & Hsame2).
    rewrite R1.
    (* the three regions kept across the memcpy (dest disjoint from FILE/stack; memcpy window below) *)
    assert (RK1 : forall a, spZ regs - 64 <= a < spZ regs -> aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms1) a).
    { intros a Ha. apply Hkeep2.
      - lia.
      - intros Hd'. destruct (Hdwr a ltac:(lia)) as [_ Hns]. apply Hns. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
      - rewrite Hspc. unfold ESTACK. lia. }
    assert (RK2 : forall a, f <= a < f + 136 -> aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms1) a).
    { intros a Ha. apply Hkeep2.
      - change SRC_FILE_BLOCK with 1304 in Hfceil. lia.
      - intros Hd'. change SRC_FILE_BLOCK with 1304 in Hdf. lia.
      - rewrite Hspc. change SRC_FILE_BLOCK with 1304 in Hfceil.
        unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hac2 |- *. lia. }
    assert (RK3 : forall a, f + 136 <= a < f + 1304 -> aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms1) a).
    { intros a Ha. apply Hkeep2.
      - change SRC_FILE_BLOCK with 1304 in Hfceil. lia.
      - intros Hd'. change SRC_FILE_BLOCK with 1304 in Hdf. lia.
      - rewrite Hspc. change SRC_FILE_BLOCK with 1304 in Hfceil.
        unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hac2 |- *. lia. }
    (* reseat at 0x8eee4 keeping fread's frame and both FILE regions (memcpy left them) *)
    lazymatch type of HS0 with st_ok _ ?Ev ?ssc ?msc =>
      let rs := eval vm_compute in (ss_mem ssc) in
      assert (Hkept : Forall (region_kept segs Ev (ms_mem msc) (mrestrict (w_H W) mem2)) rs)
        by (cbn [ms_mem restrict];
            apply Forall_cons;
              [ apply (frd_region_kept_av Ev (w_H W) (ms_mem ms1) mem2 2%nat (spZ regs) (-64) 0 (-64) 0);
                [exact VB2 | intros aa Haa; apply RK1; lia | exact Hpres2] |];
            apply Forall_cons;
              [ apply (frd_region_kept_av Ev (w_H W) (ms_mem ms1) mem2 13%nat f 0 136 8 16);
                [exact VB13 | intros aa Haa; apply RK2; lia | exact Hpres2] |];
            apply Forall_cons;
              [ apply (frd_region_kept_av Ev (w_H W) (ms_mem ms1) mem2 13%nat f 136 1304 136 140);
                [exact VB13 | intros aa Haa; apply RK3; lia | exact Hpres2] |];
            apply Forall_nil);
      pose proof (fr_after_call segs val 36%nat Ev ssc msc regs2 (mrestrict (w_H W) mem2) rs 136
        HEI0 ltac:(lia) HS0 ltac:(vm_compute; reflexivity) ltac:(cbv; lia)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HPR2 Hkept) as HSa;
      let ss2 := eval vm_compute in (ss_after_call ssc rs 36 136) in
      change (ss_after_call ssc rs 36 136) with ss2 in HSa
    end.
    rewrite <- restrict_mkst_fx in HSa.
    pose proof (fr_img_env_havoc val _ 36 (map (getr regs2) CLOB) HEI0 ltac:(rewrite length_map; cbv; lia)) as HEIa.
    pose proof (frd_base_havoc E 36 (map (getr regs2) CLOB) 2 (spZ regs) ltac:(lia) VB2) as VB2a.
    pose proof (frd_base_havoc E 36 (map (getr regs2) CLOB) 13 f ltac:(lia) VB13) as VB13a.
    clear HS0 Hkept SHOK HJ. rename HSa into HS0. rename HJ2 into HJ.
    assert (SHOK : sh_ok segs (SLit 0) (@nil shent)
      (havoc E 36 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2)) by apply Forall_nil.
    frd_run RUNF HS0 HJ SHOK.
    { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
      rewrite ?VB2a, ?VB13a in Hr0; apply AWRgen; lia. }
    (* 0x8eef8 beqz s4 (s4 = nm - |Wl|): not taken since |Wl| < nm *)
    assert (HE11h : ew (havoc E 36 (map (getr regs2) CLOB)) 11 = w64 1) by (apply frd_ew_havoc; [lia | exact HE11]).
    assert (HE12h : ew (havoc E 36 (map (getr regs2) CLOB)) 12 = w64 nm) by (apply frd_ew_havoc; [lia | exact HE12]).
    assert (HE32h : ew (havoc E 36 (map (getr regs2) CLOB)) 32 = w64 rp) by (apply frd_ew_havoc; [lia | exact HE32]).
    assert (HE33h : ew (havoc E 36 (map (getr regs2) CLOB)) 33 = w64 re) by (apply frd_ew_havoc; [lia | exact HE33]).
    assert (Hs4v : sv_denot (havoc E 36 (map (getr regs2) CLOB))
      (SAlu ALU_SUB (SMd M_MUL (SOff 12 0) (SOff 11 0)) (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0)))
      = w64 (nm - Z.of_nat (length Wl))).
    { cbn [sv_denot]. rewrite HE11h, HE12h, HE32h, HE33h. unfold w64.
      rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
      rewrite (frd_win_val rp re (-1)) by first [lia | (vm_compute; reflexivity)].
      rewrite m_mul, (v_mul_one nm) by lia.
      rewrite alu_sub. unfold v_sub. rewrite (unsigned_lit_small nm) by lia. rewrite (unsigned_lit_small (re - rp)) by lia.
      f_equal. lia. }
    frd_branch_auto; clear HS0; intros Hc4 HS0.
    * exfalso. cbn [branch_taken] in Hc4. rewrite Hs4v in Hc4. cbn [sv_denot] in Hc4.
      unfold w64 in Hc4. apply bv_eqb_eq in Hc4. apply (f_equal bv_unsigned) in Hc4.
      rewrite !unsigned_lit_small in Hc4 by lia. lia.
    * (* s4 > 0: run through the loop head to the __toread call *)
      frd_run RUNF HS0 HJ SHOK.
      { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
        destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
        rewrite ?VB2a, ?VB13a in Hr0; apply AWRgen; lia. }
      (* ===== Stage 2: the __toread call (stream drained to p + |Wl|) ===== *)
      (* memory agreement memc -> ms3: UN (memc->ms1), Hkeep2 (ms1->mem2), the two runs (mem2->ms3) *)
      pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr2
        ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
              repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2a, ?VB13a in Hrr; unfold ZS; lia|]);
              destruct Hin)) as U3.
      pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZS HFr3
        ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
              repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2a, ?VB13a in Hrr; unfold ZS; lia|]);
              destruct Hin)) as U4.
      assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ ZS a -> aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem2 a).
      { intros a Ha Hz. rewrite (U4 a Ha Hz), (U3 a Ha Hz). reflexivity. }
      clear U3 U4.
      assert (AVX : forall a, 0 <= a < 2 ^ 64 -> ~ ZS a -> ~ (d <= a < d + Z.of_nat (length Wl)) -> a < alloc_ceiling ->
        aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memc a).
      { intros a Ha Hz Hdd Hac. rewrite (UN2 a Ha Hz).
        rewrite (Hkeep2 a Ha Hdd ltac:(rewrite Hspc; unfold ESTACK;
          unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hac2; lia)).
        apply (UN a Ha Hz). }
      assert (HdestNoImg : forall a, in_img segs a -> ~ (d <= a < d + nm)).
      { intros a Hi [Hd1 Hd2]. pose proof (segs_low a Hi) as Hlo.
        destruct Hdat as [(cid & pos & Hinf & Hrng) | [(Hsl & Hsh) | (bb & nn & Hbin & Hbl & Hbh)]].
        - pose proof (Hrng a ltac:(lia)) as Hfr. unfold in_zr, frame_rng in Hfr. cbn [fst snd] in Hfr.
          exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hinf Hfr Hi).
        - pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstklo & _).
          unfold kLowMemEnd in Hlo. lia.
        - pose proof (req_size_pos nn ltac:(lia)) as (_ & Hreq).
          exact (blk_img segs B LAWS lyc Sc W memc mdc bb nn a HAR Hbin ltac:(lia) Hi). }
      assert (AGimg3 : forall a, in_img segs a -> aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memc a).
      { intros a Hi. pose proof (segs_low a Hi) as Hlo. apply AVX.
        - unfold kLowMemEnd in Hlo. lia.
        - unfold ZS. intros Hz. destruct Hz as [Hz | Hz].
          + unfold kLowMemEnd in Hlo. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hac2. lia.
          + apply (blk_img segs B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK a HAR Hblkf); [|exact Hi].
            rewrite RQ. change SRC_FILE_BLOCK with 1304 in *. lia.
        - intros Hdd. apply (HdestNoImg a Hi). lia.
        - unfold kLowMemEnd in Hlo. lia. }
      (* the four agreements asource_at_drain asks for, memc -> ms3 *)
      assert (FA3 : forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 8 <= a < f + 16) -> ~ (f + 136 <= a < f + 140) ->
        mbyte segs (rd W (ms_mem ms3)) a = mbyte segs (rd W memc) a).
      { intros a Ha H1 H2. apply (mbyte_of_aview segs). apply AVX.
        - change SRC_FILE_BLOCK with 1304 in *. lia.
        - unfold ZS. change SRC_FILE_BLOCK with 1304 in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hac2.
          intros [Hz | [Hz | Hz]]; [lia | apply H1; exact Hz | apply H2; exact Hz].
        - change SRC_FILE_BLOCK with 1304 in *. destruct Hdf as [Hdj | Hdj]; lia.
        - change SRC_FILE_BLOCK with 1304 in *. lia. }
      assert (BA3 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W (ms_mem ms3)) a = mbyte segs (rd W memc) a).
      { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
        pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as (_ & Hreq).
        intros a Ha. apply (mbyte_of_aview segs). apply AVX.
        - lia.
        - unfold ZS. change SRC_FILE_BLOCK with 1304 in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hac2.
          destruct Hdisjfb as [Hdj | Hdj]; lia.
        - destruct Hdb as [Hdj | Hdj]; lia.
        - lia. }
      assert (EA3 : forall a, asrc_env_addr K a -> mbyte segs (rd W (ms_mem ms3)) a = mbyte segs (rd W memc) a).
      { intros a Ha. apply (mbyte_of_aview segs). apply AGimg3.
        apply (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))). }
      assert (OA3 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W (ms_mem ms3)) a = mbyte segs (rd W memc) a).
      { intros a Ha. apply (mbyte_of_aview segs). apply AGimg3.
        apply (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))). }
      (* the FILE cells at the call, off the symbolic state *)
      assert (HE35h : ew (havoc E 36 (map (getr regs2) CLOB)) 35 = w64 mdv) by (apply frd_ew_havoc; [lia | exact HE35]).
      lazymatch type of HS0 with st_ok _ ?Ev ?ss ?msr =>
        pose proof (st_ok_mem_ok segs Ev ss msr HS0) as (_ & HRS & _) end.
      cbn [ss_mem restrict mkst ms_mem setpc] in HRS.
      pose proof (Forall_inv (Forall_inv_tail HRS)) as HR1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HRS))) as HR2.
      destruct HR1 as (_ & _ & _ & HC1). destruct HR2 as (_ & _ & _ & HC2c).
      cbn [YP09.r_base YP09.r_chunks] in HC1, HC2c. rewrite VB13a in HC1, HC2c.
      pose proof (Forall_inv HC1) as CK8.
      pose proof (Forall_inv (Forall_inv_tail HC1)) as CK16.
      pose proof (Forall_inv HC2c) as CK136.
      assert (N8 : val_mem segs (rd W (ms_mem ms3)) (f + 8) 8 re).
      { apply (val_of_chunk_ok segs _ _ _ 8 8%N
          (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit 18446744073709551616)) (SOff 33 0)) re CK8);
        [ cbn [sv_denot]; rewrite HE32h, HE33h; unfold w64; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned;
          apply frd_rpos_val; lia
        | cbn; lia | cbn; lia ]. }
      assert (N16 : val_mem segs (rd W (ms_mem ms3)) (f + 16) 8 re).
      { apply (val_of_chunk_ok segs _ _ _ 16 8%N (SOff 33 0) re CK16);
        [cbn [sv_denot]; rewrite HE33h; unfold w64; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
      assert (N136 : val_mem segs (rd W (ms_mem ms3)) (f + 136) 4 U32M1).
      { apply (frd_chunk_val4 _ _ _ _ _ CK136). intros i Hi.
        cbn [sv_denot]. rewrite HE35h.
        destruct Hmdcase as [-> | ->]; unfold U32M1;
        (assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia);
        destruct Hi' as [-> | [-> | [-> | ->]]]; apply bv_eq; vm_compute; reflexivity. }
      (* the drained window: rpos = rend = re *)
      assert (Hwin3 : source_window segs (rd W (ms_mem ms3)) f []).
      { right. exists (re - f - SRC_BUF_OFF). cbn [length Z.of_nat].
        split; [change SRC_BUF_OFF with 280 in *; lia|].
        split; [change SRC_BUF_OFF with 280 in *; change SRC_BUFSIZ with 1024 in *; change SRC_FILE_BLOCK with 1304 in *; lia|].
        split; [replace (f + SRC_BUF_OFF + (re - f - SRC_BUF_OFF)) with re by lia; exact N8|].
        split; [replace (f + SRC_BUF_OFF + (re - f - SRC_BUF_OFF) + Z.of_nat 0) with re by lia; exact N16|].
        apply garr8_nil. }
      (* the entry stream with its window named, and fl = 8 on this path *)
      assert (HAW : asource_at_w segs K (rd W memc) f b C p Wl).
      { exists cpos, fl, mdv. cbv zeta. (* POS *)
        exact (conj Hp0 (conj Hpc (conj Hcn (conj Hnlt (conj Hbw (conj Hcpos (conj HWl (conj Hbok (conj Hgarr (conj HST
          (conj HWIN (conj HFL (conj HEOF (conj HMD (conj HCK (conj HENV (conj HOFL Hfnz))))))))))))))))). }
      assert (Hfl8 : fl = 8).
      { destruct (proj2 HFL) as [-> | Hf24]; [reflexivity|]. exfalso. specialize (HEOF Hf24). lia. }
      assert (Hfl3 : source_flags segs (rd W (ms_mem ms3)) f 8).
      { rewrite <- Hfl8. apply (source_flags_frame segs (rd W memc) (rd W (ms_mem ms3)) f fl);
          [intros x Hx; apply FA3; [change SRC_FILE_BLOCK with 1304 in *; lia | lia | lia] | exact HFL]. }
      assert (HAT3 : asource_at segs K (rd W (ms_mem ms3)) f b C (p + Z.of_nat (length Wl))).
      { apply (asource_at_drain segs K (rd W memc) (rd W (ms_mem ms3)) f b C p Wl (Z.of_nat (length Wl)) U32M1 HAW).
        - lia.
        - replace (skipn (Z.to_nat (Z.of_nat (length Wl))) Wl) with (@nil Z) by (rewrite Nat2Z.id; symmetry; apply skipn_all).
          exact Hwin3.
        - intros a Ha H1 H2. apply FA3; assumption.
        - split; [exact N136 | right; reflexivity].
        - exact BA3.
        - exact EA3.
        - exact OA3. }
      assert (Hunbuf3 : asource_unbuffered segs K (rd W (ms_mem ms3)) f b C (p + Z.of_nat (length Wl)))
        by (split; [exact HAT3 | exact Hwin3]).
      (* the live registers at the __toread call *)
      assert (HE2h : ew (havoc E 36 (map (getr regs2) CLOB)) 2 = getr regs 2) by (apply frd_ew_havoc; [lia | exact HE2]).
      assert (HE3h : ew (havoc E 36 (map (getr regs2) CLOB)) 3 = getr regs 3) by (apply frd_ew_havoc; [lia | exact HE3]).
      assert (HE4h : ew (havoc E 36 (map (getr regs2) CLOB)) 4 = getr regs 4) by (apply frd_ew_havoc; [lia | exact HE4]).
      assert (HE13h : ew (havoc E 36 (map (getr regs2) CLOB)) 13 = w64 f).
      { apply frd_ew_havoc; [lia|]. unfold E. rewrite (Eimg_low val _ 13%nat ltac:(cbv [A_TEXT]; lia)).
        rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl). exact G13. }
      frd_reg0 HS0 (1%bv : bv 5) T1x. frd_reg0 HS0 (2%bv : bv 5) T2x.
      frd_reg0 HS0 (3%bv : bv 5) T3x. frd_reg0 HS0 (4%bv : bv 5) T4x.
      frd_reg0 HS0 (8%bv : bv 5) T8x. frd_reg0 HS0 (10%bv : bv 5) T10x.
      assert (Rra : getr (ms_regs ms3) 1 = Z_to_bv 64 (BASE + 168)).
      { rewrite T1x. change (SOff 240 168) with (SOff A_TEXT 168). exact (fr_codeptr_val val _ 168 HEIa). }
      assert (Hspc3 : spZ (ms_regs ms3) = spZ regs - 64).
      { unfold spZ in *. rewrite T2x. cbn [sv_denot]. rewrite HE2h. rewrite unsigned_lit_small by lia. lia. }
      assert (Rgp3 : getr (ms_regs ms3) 3 = w64 (as_gp B)).
      { rewrite T3x. cbn [sv_denot]. rewrite HE3h, Hgp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (Rtp3 : getr (ms_regs ms3) 4 = w64 (as_tp B)).
      { rewrite T4x. cbn [sv_denot]. rewrite HE4h, Htp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (Ra03 : getr (ms_regs ms3) 10 = w64 f).
      { rewrite T10x. cbn [sv_denot]. rewrite HE13h. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (Rs0v3 : getr (ms_regs ms3) 8 = w64 f).
      { rewrite T8x. cbn [sv_denot]. rewrite HE13h. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (Rs03 : s0Z (ms_regs ms3) = f)
        by (unfold s0Z; rewrite Rs0v3; unfold w64; apply fa_u64_small; change SRC_FILE_BLOCK with 1304 in *; lia).
      clear T1x T2x T3x T4x T8x T10x.
      assert (Hra_rng168 : 0 <= val A_TEXT + 168 < 2 ^ 64) by (destruct HBok as (_ & Hhi & _); lia).
      assert (Hra_ev168 : (val A_TEXT + 168) mod 2 = 0).
      { destruct HBok as (_ & _ & Hm4).
        pose proof (Z_div_mod_eq_full (val A_TEXT) 4) as Hd. rewrite Hm4, Z.add_0_r in Hd.
        rewrite Hd. replace (4 * (val A_TEXT / 4) + 168) with ((2 * (val A_TEXT / 4) + 84) * 2) by ring.
        apply Z_mod_mult. }
      assert (Hret3 : YK0s.ret_ok (getr (ms_regs ms3) 1%bv)).
      { unfold YK0s.ret_ok. rewrite Rra. unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by exact Hra_rng168.
        rewrite Z.add_0_r. rewrite YK0s.land_m2_even by exact Hra_ev168. reflexivity. }
      assert (Hra4096 : 4096 <= val A_TEXT + 168 < 2 ^ 64) by (split; [lia | exact (proj2 Hra_rng168)]).
      (* the __toread call *)
      lazymatch type of HS0 with st_ok ?sg ?Ev ?ssx (restrict ?HH ?msr) =>
        rewrite (st_ok_restrict_mkst sg HH Ev ssx msr HS0 ltac:(vm_compute; reflexivity));
        replace (ss_pc ssx) with (sigma FS_toread) by (vm_compute; reflexivity) end.
      eapply SRr_bind.
      { apply (frd_call_toread segs B K LAWS segs_low (sigma FS_toread) HTOREAD
                 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms3) _ k regs (ms_regs ms3) []
                 f b (p + Z.of_nat (length Wl)) 8 (val A_TEXT + 168) C HJ Hspc3 Hal16 Hstk1 Hsple Rra
                 Hret3 Hra4096 Rgp3 Rtp3
                 ltac:(apply achain_low; rewrite Rs03; change SRC_FILE_BLOCK with 1304 in *; lia)
                 Ra03 Hblkf Hblkb Hbstk Hunbuf3 Hfl3 HWRF). }
      intros W4 c4 Hle4 (ly4 & S4 & regs4 & mem4 & md4 & Hcfg4 & HJ4 & HJt & HPpres4 & Htopost).
      subst c4. rewrite Rra.
      destruct Htopost as (-> & -> & Ha0t & Hunb4 & Hfl4 & Hmd4 & Hrp4 & Hre4 & Hband4).
      pose proof HJt as (_ & _ & _ & _ & Hiot & _ & _ & _ & G1t & _ & _ & _ & _ & _ & Hstkt & _ & _).
      pose proof HJ4 as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _ & _ & _).
      pose proof HJ as (HARc & _).
      assert (KST : forall a, spZ regs + -64 <= a < spZ regs + 0 ->
        aview segs (w_H W4) mem4 a = aview segs (w_H W) (ms_mem ms3) a).
      { intros a Ha. apply G1t.
        - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
        - rewrite Hspc3. lia. }
      assert (KPR : forall a, spZ regs + -64 <= a < spZ regs + 0 -> apresent (w_H W4) mem4 a).
      { intros a Ha. apply Hpres4. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      (* what the path kept from fread's entry to the __toread call *)
      assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RFREAD_STK <= a < spZ regs) -> ~ rread_wrset f d nm a ->
        aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memc a).
      { intros a Ha Hw Hwr. unfold rread_wrset in Hwr. change SRC_FILE_BLOCK with 1304 in Hwr.
        unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hw.
        assert (HnZ : ~ ZS a) by (unfold ZS; intros Hz; lia).
        rewrite (UN2 a Ha HnZ).
        rewrite (Hkeep2 a Ha ltac:(lia) ltac:(rewrite Hspc; unfold ESTACK; lia)).
        exact (UN a Ha HnZ). }
      assert (APG3 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms3) a).
      { intros a Ha. apply (fr_apresent_grows _ (ms_mem ms2)); [exact HG3|].
        apply (fr_apresent_grows _ mem2); [exact HG2|]. apply Hpres2.
        apply (fr_apresent_grows _ (ms_mem ms0)); [exact HG1|].
        apply (fr_apresent_grows _ (ms_mem ms)); [exact HG0|].
        apply (fr_apresent_grows _ memc); [exact HG|exact Ha]. }
      assert (APW3 : forall a, spZ regs - RFREAD_STK <= a < spZ regs -> apresent (w_H W) (ms_mem ms3) a).
      { intros a Ha. apply APG3. apply Hpres0. lia. }
      assert (K1 : rread_kept segs B RFREAD_STK lyc Sc W memc W (ms_mem ms3) (spZ regs) (rread_wrset f d nm)).
      { apply (frd_kept_of_agree_all segs B LAWS RFREAD_STK lyc Sc W memc mdc W (ms_mem ms3) (spZ regs) (rread_wrset f d nm) HAR);
        [unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia | exact AG3 | exact AGimg3 | exact APG3 | exact APW3]. }
      assert (Hcl : ~ YI16.sink_open_fp (rtoread_fp f))
        by (apply sink_closed_pos; constructor; [cbn [fst]; lia | constructor]).
      assert (K2 : rread_kept segs B RTOREAD_STK lyc Sc W (ms_mem ms3) W4 mem4 (spZ (ms_regs ms3))
                     (fun a => f <= a < f + SRC_FILE_BLOCK)).
      { apply (frd_kept_of_acall segs B).
        apply (acall_kept_of_journal segs B segs_low RTOREAD_STK (spZ (ms_regs ms3)) (rtoread_fp f) [] lyc Sc W (ms_mem ms3) _
                 lyc Sc W4 mem4 md4 0 (fun a => f <= a < f + SRC_FILE_BLOCK) HJt HARc); [| | exact Hcl].
        - intros a (r & Hr & Ha). unfold rtoread_fp in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact Ha.
        - intros bb m i Hb _ _. exact Hb. }
      assert (K12 : rread_kept segs B RFREAD_STK lyc Sc W memc W4 mem4 (spZ regs) (rread_wrset f d nm)).
      { apply (frd_kept_trans segs B RFREAD_STK RTOREAD_STK RFREAD_STK lyc Sc W memc W (ms_mem ms3) W4 mem4
                 (spZ regs) (spZ (ms_regs ms3)) (spZ regs) (rread_wrset f d nm) (fun a => f <= a < f + SRC_FILE_BLOCK)
                 (rread_wrset f d nm) K1 K2).
        - lia.
        - lia.
        - rewrite Hspc3. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK. lia.
        - rewrite Hspc3. lia.
        - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
        - lia.
        - intros a Ha. apply Hpres0. lia.
        - intros a Ha. exact Ha.
        - intros a Ha. left. exact Ha. }
      assert (BAND1 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
        aview segs (w_H W) (ms_mem ms3) s = aview segs (w_H W) memc s).
      { apply (frd_band_of_low segs B LAWS lyc Sc W memc mdc W (ms_mem ms3) f d nm HAR Hblkf Hdam).
        intros a Ha Hn. apply AG3; [lia | unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia | exact Hn]. }
      assert (BAND12 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
        aview segs (w_H W4) mem4 s = aview segs (w_H W) memc s)
        by (intros s Hs; rewrite (Hband4 s Hs); exact (BAND1 s Hs)).
      destruct (aos_step_closed _ _ _ Hcl Hiot) as (Hfd4 & Hfs4 & _ & _).
      unfold same_but_materialized in Hsame2.
      assert (Hfds4 : m_fds md4 = m_fds mdc) by (unfold m_fds; rewrite Hfd4, Hsame2; reflexivity).
      assert (Hfss4 : m_fs md4 = m_fs mdc) by (unfold m_fs; rewrite Hfs4, Hsame2; reflexivity).
      (* reseat at the return 0x8ef04: keep fread's frame, havoc the caller-saved registers *)
      lazymatch type of HS0 with st_ok _ ?Ev ?ssc ?msc =>
        let rs := eval vm_compute in (pick (ss_mem ssc) [0%nat]) in
        assert (Hkept : Forall (region_kept segs Ev (ms_mem msc) (mrestrict (w_H W4) mem4)) rs)
          by (cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
              apply (frd_region_kept Ev W W4 (ms_mem ms3) mem4 2%nat (spZ regs)); [exact VB2a | exact KST | exact KPR]);
        pose proof (fr_after_call segs val 56%nat Ev ssc msc regs4 (mrestrict (w_H W4) mem4) rs 168
          HEIa ltac:(lia) HS0 ltac:(vm_compute; reflexivity) ltac:(cbv; lia)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HPpres4 Hkept) as HSa;
        let ss2 := eval vm_compute in (ss_after_call ssc rs 56 168) in
        change (ss_after_call ssc rs 56 168) with ss2 in HSa
      end.
      rewrite <- restrict_mkst_fx in HSa.
      clear HS0 Hkept.
      pose proof (fr_img_env_havoc val _ 56 (map (getr regs4) CLOB) HEIa ltac:(rewrite length_map; cbv; lia)) as HEIb.
      pose proof (frd_base_havoc _ 56 (map (getr regs4) CLOB) 13 f ltac:(lia) VB13a) as VB13b.
      pose proof (frd_base_havoc _ 56 (map (getr regs4) CLOB) 2 (spZ regs) ltac:(lia) VB2a) as VB2b.
      assert (HE34 : ew E 34 = w64 (as_read K))
        by (unfold E; rewrite (Eimg_low val _ 34%nat ltac:(cbv [A_TEXT]; lia)); exact (ew_Ereg_extra regs _ 2)).
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 34 _ ltac:(lia)
        (frd_ew_havoc E 36 (map (getr regs2) CLOB) 34 _ ltac:(lia) HE34)) as HE34b.
      pose proof Hunb4 as ((Wl4 & cpos4 & fl4 & md4x & _ & _ & _ & _ & _ & _ & _ & _ & _ & HST4 & _) & Hwin4).
      pose proof HST4 as (_ & Hread4 & _).
      (* the FILE cell the code reads next: f->read at +64 *)
      pose proof (fr_add_region segs val _ _ _
        (YP09.mkRegion (Some 13%nat) 0 1304 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 34 0))]) HSa
        ltac:(vm_compute; reflexivity)) as HSb.
      lazymatch type of HSb with ?A -> _ => assert (HR3 : A) end.
      { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
        rewrite VB13b. split; [lia|]. split; [change SRC_FILE_BLOCK with 1304 in *; lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs _ _ f 64 8%N (SOff 34 0) (as_read K));
          [cbn [sv_denot]; rewrite HE34b; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; destruct Hmread_pc; lia | cbn; lia | exact Hread4]. }
      specialize (HSb HR3).
      lazymatch type of HSb with ?A -> _ => assert (HD3 : A) end.
      { cbn [ss_mem all_disjoint]. repeat apply conj; try exact I;
        (unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?VB2b, ?VB13b;
         change SRC_FILE_BLOCK with 1304 in *; first [left; lia | right; lia]). }
      specialize (HSb HD3).
      clear HSa HR3 HD3.
      lazymatch type of HSb with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HSb end.
      clear SHOK.
      lazymatch type of HSb with st_ok_pi _ _ ?Eb _ _ =>
        assert (SHOK : sh_ok segs (SLit 0) (@nil shent) Eb (mrestrict (w_H W4) mem4)) by apply Forall_nil end.
      rename HSb into HS0. clear HJ. rename HJ4 into HJ.
      (* 0x8ef04 bnez a0: __toread returned 0 (flags 8) *)
      frd_branch_auto; clear HS0; intros Hc3 HS0.
      { exfalso. cbn [branch_taken sv_denot havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB] in Hc3.
        rewrite Ha0t in Hc3. vm_compute in Hc3. discriminate. }
      frd_run RUNF HS0 HJ SHOK.
      { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
        destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
        rewrite ?VB2b, ?VB13b in Hr0; [lia | apply AWRgen; lia]. }
      (* the env facts through the second reseat *)
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 2 _ ltac:(lia) HE2h) as HE2b.
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 3 _ ltac:(lia) HE3h) as HE3b.
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 4 _ ltac:(lia) HE4h) as HE4b.
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 10 _ ltac:(lia)
        (frd_ew_havoc E 36 (map (getr regs2) CLOB) 10 _ ltac:(lia) HE10)) as HE10b.
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 11 _ ltac:(lia) HE11h) as HE11b.
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 12 _ ltac:(lia) HE12h) as HE12b.
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 13 _ ltac:(lia) HE13h) as HE13b.
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 32 _ ltac:(lia) HE32h) as HE32b.
      pose proof (frd_ew_havoc _ 56 (map (getr regs4) CLOB) 33 _ ltac:(lia) HE33h) as HE33b.
      assert (Hdhi : d + nm < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hdam; lia).
      (* 0x8ef04 - 0x8ef18 wrote only fread's frame *)
      set (ZS4 := fun a => spZ regs - 64 <= a < spZ regs).
      pose proof (fr_kept_of_frame segs _ _ (w_H W4) _ _ ZS4 HFr4
        ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
              repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2b, ?VB13b in Hrr; unfold ZS4; lia|]);
              destruct Hin)) as UN4.
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ4 & _ & _ & _).
      assert (FA4 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W4 (ms_mem ms4)) a = mbyte segs (rd W4 mem4) a).
      { intros a Ha. apply (mbyte_of_aview segs). apply UN4; [change SRC_FILE_BLOCK with 1304 in *; lia|].
        unfold ZS4. change SRC_FILE_BLOCK with 1304 in *. lia. }
      assert (BA4 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W4 (ms_mem ms4)) a = mbyte segs (rd W4 mem4) a).
      { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
        pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
        intros a Ha. apply (mbyte_of_aview segs). apply UN4; [lia|]. unfold ZS4.
        unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      assert (EA4 : forall a, asrc_env_addr K a -> mbyte segs (rd W4 (ms_mem ms4)) a = mbyte segs (rd W4 mem4) a).
      { intros a Ha. apply (mbyte_of_aview segs).
        pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
        pose proof (segs_low a Hi) as Hl. apply UN4; [unfold kLowMemEnd in Hl; lia|]. unfold ZS4.
        unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      assert (OA4 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W4 (ms_mem ms4)) a = mbyte segs (rd W4 mem4) a).
      { intros a Ha. apply (mbyte_of_aview segs).
        pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
        pose proof (segs_low a Hi) as Hl. apply UN4; [unfold kLowMemEnd in Hl; lia|]. unfold ZS4.
        unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      assert (Hunbm : asource_unbuffered segs K (rd W4 (ms_mem ms4)) f b C (p + Z.of_nat (length Wl)))
        by exact (asource_unbuffered_frame segs K (rd W4 mem4) (rd W4 (ms_mem ms4)) f b C _ FA4 BA4 EA4 OA4 Hunb4).
      assert (Hflm : source_flags segs (rd W4 (ms_mem ms4)) f 8).
      { apply (source_flags_frame segs (rd W4 mem4) (rd W4 (ms_mem ms4)) f 8); [|exact Hfl4].
        intros x Hx. apply FA4. change SRC_FILE_BLOCK with 1304 in *. lia. }
      assert (Hmdm : source_mode segs (rd W4 (ms_mem ms4)) f U32M1).
      { apply (source_mode_frame segs (rd W4 mem4) (rd W4 (ms_mem ms4)) f U32M1); [|exact Hmd4].
        intros x Hx. apply FA4. change SRC_FILE_BLOCK with 1304 in *. lia. }
      assert (BAND124 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
        aview segs (w_H W4) (ms_mem ms4) s = aview segs (w_H W) memc s).
      { intros s Hs. rewrite (UN4 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND12 s Hs)|].
        unfold ZS4. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
        unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      assert (K124 : rread_kept segs B RFREAD_STK lyc Sc W memc W4 (ms_mem ms4) (spZ regs) (rread_wrset f d nm)).
      { apply (frd_kept_extend lyc Sc W memc W4 mem4 md4 (ms_mem ms4) (spZ regs) (rread_wrset f d nm) K12 HAR4).
        - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
        - lia.
        - intros a Ha. apply Hpres0. lia.
        - intros a Ha Hs. apply UN4; [exact Ha|]. unfold ZS4. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
        - intros a Ha. exact (fr_apresent_grows _ mem4 (ms_mem ms4) a HG4 Ha).
        - intros a Ha. apply HpresJ4. lia. }
      (* 0x8ef18 jalr a3: a3 = f->read = mread *)
      frd_reg HS0 (13%bv : bv 5) R13x.
      assert (R13 : getr (ms_regs ms4) 13%bv = Z_to_bv 64 (as_read K)).
      { rewrite R13x. cbn [sv_denot]. rewrite HE34b. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      apply (fr_jalr_call segs Hwx tbl tbl_ok val sigma frd_listing Hcert HBok W4 _ _ _ _ _ 0x680e7 1%bv 13%bv (as_read K)
               HEIb HS0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) frd_D_jalr ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) R13 (proj1 Hmread_pc) (proj2 Hmread_pc)).
      intros matJ msm Hmsm HSm. subst msm.
      lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ _ _; cfg_model := _ |} _ => set (regsm := rg) in * end.
      frd_reg0 HSm (1%bv : bv 5) Q1. frd_reg0 HSm (2%bv : bv 5) Q2.
      frd_reg0 HSm (3%bv : bv 5) Q3. frd_reg0 HSm (4%bv : bv 5) Q4.
      frd_reg0 HSm (8%bv : bv 5) Q8. frd_reg0 HSm (10%bv : bv 5) Q10.
      frd_reg0 HSm (11%bv : bv 5) Q11. frd_reg0 HSm (12%bv : bv 5) Q12.
      assert (Rram : getr regsm 1%bv = Z_to_bv 64 (val A_TEXT + 192))
        by (rewrite Q1; exact (fr_codeptr_val val _ 192 HEIb)).
      assert (Hspm : spZ regsm = spZ regs - 64).
      { unfold spZ in *. rewrite Q2. cbn [sv_denot]. rewrite HE2b. rewrite unsigned_lit_small by lia. lia. }
      assert (Rgpm : getr regsm 3%bv = w64 (as_gp B)).
      { rewrite Q3. cbn [sv_denot]. rewrite HE3b, Hgp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (Rtpm : getr regsm 4%bv = w64 (as_tp B)).
      { rewrite Q4. cbn [sv_denot]. rewrite HE4b, Htp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (Ra0m : getr regsm 10%bv = w64 f).
      { rewrite Q10. cbn [sv_denot]. rewrite HE13b. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (Rs0vm : getr regsm 8%bv = w64 f).
      { rewrite Q8. cbn [sv_denot]. rewrite HE13b. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      assert (Ra1m : getr regsm 11%bv = w64 (d + Z.of_nat (length Wl))).
      { rewrite Q11. cbn [sv_denot]. rewrite HE10b, HE32b, HE33b. unfold w64.
        rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
        rewrite (frd_bs_a1_val d rp re 18446744073709551615) by first [lia | (vm_compute; reflexivity)].
        f_equal. lia. }
      assert (Ra2m : getr regsm 12%bv = w64 (nm - Z.of_nat (length Wl))).
      { rewrite Q12. cbn [sv_denot]. rewrite HE11b, HE12b, HE32b, HE33b. unfold w64.
        rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
        rewrite (frd_bs_a2_val nm rp re) by lia. f_equal. lia. }
      assert (Rs0m : s0Z regsm = f)
        by (unfold s0Z; rewrite Rs0vm; unfold w64; apply fa_u64_small; change SRC_FILE_BLOCK with 1304 in *; lia).
      assert (Hra192 : 0 <= val A_TEXT + 192 < 2 ^ 64) by (destruct HBok as (_ & Hhi & _); lia).
      assert (Hra192e : (val A_TEXT + 192) mod 2 = 0).
      { destruct HBok as (_ & _ & Hm4).
        pose proof (Z_div_mod_eq_full (val A_TEXT) 4) as Hd. rewrite Hm4, Z.add_0_r in Hd.
        rewrite Hd. replace (4 * (val A_TEXT / 4) + 192) with ((2 * (val A_TEXT / 4) + 96) * 2) by ring.
        apply Z_mod_mult. }
      assert (Hretm : YK0s.ret_ok (getr regsm 1%bv)).
      { unfold YK0s.ret_ok. rewrite Rram. unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by exact Hra192.
        rewrite Z.add_0_r. rewrite YK0s.land_m2_even by exact Hra192e. reflexivity. }
      assert (Hra192b : 4096 <= val A_TEXT + 192 < 2 ^ 64) by (split; [lia | exact (proj2 Hra192)]).
      assert (Hdestm : rread_dest segs B STK sp0 FP ly S own lyc Sc W4 (ms_mem ms4) RFREAD_STK (spZ regs) d nm f b
                         (Z.of_nat (length C))).
      { apply (frd_dest_sub segs B STK sp0 FP ly S own lyc Sc W memc W4 (ms_mem ms4) RFREAD_STK (spZ regs) RFREAD_STK (spZ regs)
                 d nm d nm f b (Z.of_nat (length C)) Hdest0); try lia. exact BAND124. }
      pose proof (ajournal_materialize segs B LAWS segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W4 (ms_mem ms4) _ k matJ HJ)
        as HJm.
      (* the mread call: the rest of the request, (d + |Wl|, nm - |Wl|) at position p + |Wl| *)
      eapply SRr_bind.
      { apply (frd_call_mread segs B K HMREAD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W4 (ms_mem ms4) _ k regs regsm []
                 d nm (d + Z.of_nat (length Wl)) (nm - Z.of_nat (length Wl)) f b (p + Z.of_nat (length Wl)) U32M1
                 (val A_TEXT + 192) C
                 HJm Hspm Hal16 Hstk1 Hsple Rram Hretm Hra192b Rgpm Rtpm
                 ltac:(apply achain_low; rewrite Rs0m; change SRC_FILE_BLOCK with 1304 in *; lia)
                 Ra0m Ra1m Ra2m Hblkf Hblkb Hbstk Hunbm Hflm Hmdm HWRF ltac:(lia) Hdestm ltac:(lia) ltac:(lia)). }
      intros W5 c5 Hle5 (ly5 & S5 & regs5 & mem5 & md5 & Hcfg5 & HJ5 & HPpres5 & Kmr & Hmrpost).
      subst c5. rewrite Rram.
      destruct Hmrpost as (-> & -> & Ha0m & Hgarrm & Hatm & Hcookm & Hrpm & Hrem & Hflm5 & Hmdm5 & Hfdsm & Hfsm & Hbandm5).
      pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _ & _ & _).
      pose proof Kmr as (Kmr1 & _).
      assert (KST5 : forall a, spZ regs + -64 <= a < spZ regs + 0 ->
        aview segs (w_H W5) mem5 a = aview segs (w_H W4) (ms_mem ms4) a).
      { intros a Ha. apply Kmr1.
        - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
        - rewrite Hspm. unfold RMREAD_STK, ESTACK. lia.
        - unfold rread_wrset. intros [Hx | Hx]; [change SRC_FILE_BLOCK with 1304 in *; lia|].
          apply (proj2 (Hdwr a ltac:(lia))). unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK. lia. }
      assert (KPR5 : forall a, spZ regs + -64 <= a < spZ regs + 0 -> apresent (w_H W5) mem5 a).
      { intros a Ha. apply Hpres5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      (* reseat at the return 0x8ef1c: keep fread's frame *)
      lazymatch type of HSm with st_ok _ ?Ev ?ssc ?msc =>
        let rs := eval vm_compute in (pick (ss_mem ssc) [1%nat]) in
        assert (Hkept5 : Forall (region_kept segs Ev (ms_mem msc) (mrestrict (w_H W5) mem5)) rs)
          by (cbn [ms_mem restrict mkst]; apply Forall_cons; [|apply Forall_nil];
              apply (frd_region_kept Ev W4 W5 (ms_mem ms4) mem5 2%nat (spZ regs)); [exact VB2b | exact KST5 | exact KPR5]);
        pose proof (fr_after_call segs val 76%nat Ev ssc msc regs5 (mrestrict (w_H W5) mem5) rs 192
          HEIb ltac:(lia) HSm ltac:(vm_compute; reflexivity) ltac:(cbv; lia)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HPpres5 Hkept5) as HSc;
        let ss3 := eval vm_compute in (ss_after_call ssc rs 76 192) in
        change (ss_after_call ssc rs 76 192) with ss3 in HSc
      end.
      rewrite <- restrict_mkst_fx in HSc.
      clear HSm Hkept5 HS0.
      pose proof (fr_img_env_havoc val _ 76 (map (getr regs5) CLOB) HEIb ltac:(rewrite length_map; cbv; lia)) as HEIc.
      pose proof (frd_base_havoc _ 76 (map (getr regs5) CLOB) 2 (spZ regs) ltac:(lia) VB2b) as VB2c.
      lazymatch type of HSc with st_ok_pi _ _ ?E3 _ _ =>
        clear SHOK; assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W5) mem5)) by apply Forall_nil end.
      rename HSc into HS0. clear HJ. rename HJ5 into HJ.
      (* ===== Stage 4: mread returned Jm ===== *)
      pose proof (frd_ew_havoc _ 76 (map (getr regs5) CLOB) 2 _ ltac:(lia) HE2b) as HE2c.
      pose proof (frd_ew_havoc _ 76 (map (getr regs5) CLOB) 3 _ ltac:(lia) HE3b) as HE3c.
      pose proof (frd_ew_havoc _ 76 (map (getr regs5) CLOB) 4 _ ltac:(lia) HE4b) as HE4c.
      pose proof (frd_ew_havoc _ 76 (map (getr regs5) CLOB) 11 _ ltac:(lia) HE11b) as HE11c.
      pose proof (frd_ew_havoc _ 76 (map (getr regs5) CLOB) 12 _ ltac:(lia) HE12b) as HE12c.
      pose proof (frd_ew_havoc _ 76 (map (getr regs5) CLOB) 13 _ ltac:(lia) HE13b) as HE13c.
      pose proof (frd_ew_havoc _ 76 (map (getr regs5) CLOB) 32 _ ltac:(lia) HE32b) as HE32c.
      pose proof (frd_ew_havoc _ 76 (map (getr regs5) CLOB) 33 _ ltac:(lia) HE33b) as HE33c.
      assert (HE1 : ew E 1 = getr regs 1).
      { unfold E. rewrite (Eimg_low val _ 1%nat ltac:(cbv [A_TEXT]; lia)). exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
      pose proof (rread_k_split (Z.of_nat (length Wl)) (nm - Z.of_nat (length Wl)) (Z.of_nat (length C)) p
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HJs.
      replace (Z.of_nat (length Wl) + (nm - Z.of_nat (length Wl))) with nm in HJs by lia.
      pose proof (rread_k_bounds (nm - Z.of_nat (length Wl)) (Z.of_nat (length C)) (p + Z.of_nat (length Wl))
        ltac:(lia) ltac:(lia)) as Hkb.
      set (Jm := rread_k (nm - Z.of_nat (length Wl)) (Z.of_nat (length C)) (p + Z.of_nat (length Wl))) in *.
      lazymatch type of HE12c with ew ?E3 _ = _ =>
        assert (HE80 : ew E3 80 = w64 Jm) by (cbn [havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB]; exact Ha0m) end.
      (* what the path kept through mread *)
      assert (K45 : rread_kept segs B RFREAD_STK lyc Sc W memc W5 mem5 (spZ regs) (rread_wrset f d nm)).
      { apply (frd_kept_trans segs B RFREAD_STK RMREAD_STK RFREAD_STK lyc Sc W memc W4 (ms_mem ms4) W5 mem5
                 (spZ regs) (spZ regsm) (spZ regs) (rread_wrset f d nm)
                 (rread_wrset f (d + Z.of_nat (length Wl)) (nm - Z.of_nat (length Wl))) (rread_wrset f d nm) K124 Kmr).
        - lia.
        - lia.
        - rewrite Hspm. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK. lia.
        - rewrite Hspm. lia.
        - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
        - lia.
        - intros a Ha. apply Hpres0. lia.
        - intros a Ha. exact Ha.
        - intros a Ha. unfold rread_wrset in *. lia. }
      assert (BAND45 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
        aview segs (w_H W5) mem5 s = aview segs (w_H W) memc s)
        by (intros s Hs; rewrite (Hbandm5 s Hs); exact (BAND124 s Hs)).
      assert (Hfds5 : m_fds md5 = m_fds mdc) by (rewrite Hfdsm; exact Hfds4).
      assert (Hfss5 : m_fs md5 = m_fs mdc) by (rewrite Hfsm; exact Hfss4).
      pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HsloL & HshiL & _).
      assert (HceilL : alloc_ceiling <= ly_stk_lo lyc) by (rewrite HsloL; exact Hceil).
      assert (HhiL : ly_stk_hi lyc <= 2 ^ 64) by (rewrite HshiL; lia).
      (* the window bytes memcpy delivered at d .. d+|Wl|: kept by __toread, mread and the runs *)
      assert (HatW : rread_at B lyc Sc d (Z.of_nat (length Wl)))
        by (apply (frd_rread_at_sub lyc Sc d nm d (Z.of_nat (length Wl)) Hdat); lia).
      assert (DKm : forall x, d <= x < d + Z.of_nat (length Wl) -> aview segs (w_H W5) mem5 x = aview segs (w_H W) mem2 x).
      { intros x Hx.
        pose proof (proj2 (Hdwr x ltac:(lia))) as Hxs.
        assert (Hxr : 0 <= x < 2 ^ 64) by lia.
        transitivity (aview segs (w_H W4) (ms_mem ms4) x).
        { apply (frd_dest_kept RMREAD_STK lyc Sc W4 (ms_mem ms4) W5 mem5 (spZ regsm)
                   (rread_wrset f (d + Z.of_nat (length Wl)) (nm - Z.of_nat (length Wl))) d (Z.of_nat (length Wl))
                   Kmr HatW HceilL HhiL); [|exact Hx].
          intros a Ha. pose proof (proj2 (Hdwr a ltac:(lia))) as Has. split.
          - unfold rread_wrset. change SRC_FILE_BLOCK with 1304 in *. destruct Hdf as [Hdj | Hdj]; lia.
          - rewrite Hspm. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        transitivity (aview segs (w_H W4) mem4 x).
        { apply UN4; [exact Hxr|]. unfold ZS4. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hxs. lia. }
        transitivity (aview segs (w_H W) (ms_mem ms3) x).
        { apply (frd_dest_kept RTOREAD_STK lyc Sc W (ms_mem ms3) W4 mem4 (spZ (ms_regs ms3))
                   (fun a => f <= a < f + SRC_FILE_BLOCK) d (Z.of_nat (length Wl)) K2 HatW HceilL HhiL); [|exact Hx].
          intros a Ha. pose proof (proj2 (Hdwr a ltac:(lia))) as Has. split.
          - change SRC_FILE_BLOCK with 1304 in *. destruct Hdf as [Hdj | Hdj]; lia.
          - rewrite Hspc3. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        apply UN2; [exact Hxr|]. unfold ZS. change SRC_FILE_BLOCK with 1304 in *.
        unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hxs. destruct Hdf as [Hdj | Hdj]; lia. }
      assert (HWIN5 : garr8 segs (rd W5 mem5) d Wl).
      { rewrite <- (firstn_all Wl).
        apply (frd_garr8_copy (rd W memc) (rd W5 mem5) rp d Wl (length Wl) Hgarrw (le_n _)).
        intros i Hi.
        apply (frd_mbyte_of_aview2 (w_H W) (w_H W5) memc mem5 (rp + i) (d + i)).
        rewrite (DKm (d + i) ltac:(lia)).
        rewrite (Hcopy2 i Hi).
        apply UN; [change SRC_FILE_BLOCK with 1304 in *; change SRC_BUF_OFF with 280 in *; lia|].
        unfold ZS. change SRC_FILE_BLOCK with 1304 in *. change SRC_BUF_OFF with 280 in *.
        unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      (* the bytes fread delivers: the window, then what mread delivered *)
      pose proof (frd_firstn_window C Wl p cpos (Z.of_nat (length Wl)) HWl ltac:(lia)) as HFW.
      rewrite Nat2Z.id, firstn_all in HFW.
      rewrite Z2Nat.inj_add, Nat2Z.id in Hgarrm by lia.
      assert (HASM : forall (Wf : world segs) memf,
        (forall x, d <= x < d + nm -> aview segs (w_H Wf) memf x = aview segs (w_H W5) mem5 x) ->
        garr8 segs (rd Wf memf) d (firstn (Z.to_nat (rread_k nm (Z.of_nat (length C)) p)) (skipn (Z.to_nat p) C))).
      { intros Wf memf DKF. rewrite <- HJs.
        replace (Z.to_nat (Jm + Z.of_nat (length Wl))) with (length Wl + Z.to_nat Jm)%nat by lia.
        rewrite frd_firstn_skipn_app, HFW.
        apply garr8_app. split.
        - apply (garr8_frame segs (rd W5 mem5) (rd Wf memf) d Wl HWIN5).
          intros x Hx. apply (mbyte_of_aview segs). apply DKF. lia.
        - apply (garr8_frame segs (rd W5 mem5) (rd Wf memf) _ _ Hgarrm).
          intros x Hx. rewrite length_firstn, length_skipn in Hx. apply (mbyte_of_aview segs). apply DKF. lia. }
      (* 0x8ef1c beqz a0: a0 = Jm *)
      frd_branch_auto; clear HS0; intros Hk4 HS0.
      { (* Jm = 0: return (s6 - s4) / s1 = |Wl| (0x8ef50) *)
        assert (Hj0 : Jm = 0).
        { pose proof Hk4 as Hcp. cbn [branch_taken sv_denot havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB] in Hcp.
          rewrite Ha0m in Hcp. unfold w64 in Hcp. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hcp.
          apply bv_eqb_eq in Hcp. apply (f_equal bv_unsigned) in Hcp.
          rewrite !unsigned_lit_small in Hcp by lia. exact Hcp. }
        frd_run RUNF HS0 HJ SHOK.
        { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
          destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
          rewrite ?VB2c in Hr0; apply AWRgen; lia. }
        eapply (RETF W5 _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity)).
        intros matR.
        set (ZS5 := fun a => spZ regs - 64 <= a < spZ regs).
        pose proof (fr_kept_of_frame segs _ _ (w_H W5) _ _ ZS5 HFr5
          ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2c in Hrr; unfold ZS5; lia|]);
                destruct Hin)) as UN5.
        pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & _ & _ & _).
        frd_reg HS0 (1%bv : bv 5) R1x.
        assert (RF1 : getr (ms_regs ms5) 1 = getr regs 1).
        { rewrite R1x. cbn [sv_denot]. rewrite !ew_havoc_old by lia. rewrite HE1, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
        assert (HPR : aregs_preserved regs (ms_regs ms5)).
        { lazymatch type of HS0 with st_ok_pi _ _ ?Ex ?ss _ =>
            exact (aregs_preserved_of_st_ok segs (w_H W5) Ex (abs_ss val ss) ms5 regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]
                     HS0 (frd_ea_havoc2 _ _ 76 _ (frd_ea_havoc2 _ _ 56 _ (frd_ea_havoc val regs _ 36 _ ltac:(lia)) ltac:(lia))
                            ltac:(lia))
                     ltac:(vm_compute; reflexivity)) end. }
        frd_reg HS0 (10%bv : bv 5) R10x.
        assert (RF10 : getr (ms_regs ms5) 10 = w64 (rread_k nm (Z.of_nat (length C)) p)).
        { rewrite R10x, denot_lit_U.
          rewrite (frd_bs_U_ret _ nm (nm - (re - rp)) _ HE12c HE11c ltac:(lia)
                    (frd_bs_U_s4 _ nm rp re HE12c HE11c HE32c HE33c ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                    ltac:(lia)).
          unfold w64. f_equal. lia. }
        assert (FA5 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W5 (ms_mem ms5)) a = mbyte segs (rd W5 mem5) a).
        { intros a Ha. apply (mbyte_of_aview segs). apply UN5; [change SRC_FILE_BLOCK with 1304 in *; lia|].
          unfold ZS5. change SRC_FILE_BLOCK with 1304 in *. lia. }
        assert (BA5 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W5 (ms_mem ms5)) a = mbyte segs (rd W5 mem5) a).
        { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
          pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
          intros a Ha. apply (mbyte_of_aview segs). apply UN5; [lia|]. unfold ZS5.
          unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        assert (EA5 : forall a, asrc_env_addr K a -> mbyte segs (rd W5 (ms_mem ms5)) a = mbyte segs (rd W5 mem5) a).
        { intros a Ha. apply (mbyte_of_aview segs).
          pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
          pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
          unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        assert (OA5 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W5 (ms_mem ms5)) a = mbyte segs (rd W5 mem5) a).
        { intros a Ha. apply (mbyte_of_aview segs).
          pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
          pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
          unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        assert (HAT : asource_at segs K (rd W5 (ms_mem ms5)) f b C (p + rread_k nm (Z.of_nat (length C)) p)).
        { replace (p + rread_k nm (Z.of_nat (length C)) p) with (p + Z.of_nat (length Wl) + Jm) by lia.
          exact (asource_at_frame segs K (rd W5 mem5) (rd W5 (ms_mem ms5)) f b C _ FA5 BA5 EA5 OA5 Hatm). }
        assert (HMD5 : source_mode segs (rd W5 (ms_mem ms5)) f U32M1).
        { apply (source_mode_frame segs (rd W5 mem5) (rd W5 (ms_mem ms5)) f U32M1); [|exact Hmdm5].
          intros a Ha. apply FA5. change SRC_FILE_BLOCK with 1304 in *. lia. }
        assert (KF : rread_kept segs B RFREAD_STK lyc Sc W memc W5 (ms_mem ms5) (spZ regs) (rread_wrset f d nm)).
        { apply (frd_kept_extend lyc Sc W memc W5 mem5 md5 (ms_mem ms5) (spZ regs) (rread_wrset f d nm) K45 HAR5).
          - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
          - lia.
          - intros a Ha. apply Hpres0. lia.
          - intros a Ha Hs. apply UN5; [exact Ha|]. unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
          - intros a Ha. exact (fr_apresent_grows _ mem5 (ms_mem ms5) a HG5 Ha).
          - intros a Ha. apply HpresF. lia. }
        assert (DKF : forall x, d <= x < d + nm -> aview segs (w_H W5) (ms_mem ms5) x = aview segs (w_H W5) mem5 x).
        { intros x Hx. pose proof (proj2 (Hdwr x Hx)) as Hxs. apply UN5; [lia|].
          unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hxs. lia. }
        unfold rread_post_base.
        eexists lyc, Sc, (ms_regs ms5), (ms_mem ms5), _.
        split; [rewrite RF1, (fr_ret_of_ok _ Hra); reflexivity|].
        split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ|].
        split; [exact HPR|].
        split; [exact KF|].
        unfold rfread_post. cbv zeta.
        split; [reflexivity|]. split; [reflexivity|].
        split; [exact RF10|].
        split; [exact (HASM W5 (ms_mem ms5) DKF)|].
        split; [exact HAT|].
        split; [exact HMD5|].
        split; [intros Hz; exfalso; lia|].
        split; [exact Hfds5|]. split; [exact Hfss5|].
        intros s Hs. rewrite (UN5 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND45 s Hs)|].
        unfold ZS5. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
        unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      (* Jm <> 0: s4 -= Jm, then 0x8ef28 bnez s4 *)
      frd_run RUNF HS0 HJ SHOK.
      { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
        destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
        rewrite ?VB2c in Hr0; apply AWRgen; lia. }
      set (ZS5 := fun a => spZ regs - 64 <= a < spZ regs).
      pose proof (fr_kept_of_frame segs _ _ (w_H W5) _ _ ZS5 HFr5
        ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
              repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2c in Hrr; unfold ZS5; lia|]);
              destruct Hin)) as U5.
      frd_branch_auto; clear HS0; intros Hk5 HS0.
      { (* s4 <> 0: Jm < nm - |Wl|, so mread hit the end, set F_EOF and left the window empty; back to __toread *)
        assert (Hjlt : Jm < nm - Z.of_nat (length Wl)).
        { pose proof Hk5 as Hcp. rewrite !denot_lit_U in Hcp.
          rewrite (frd_bs_U_s4k _ nm rp re Jm 80 HE12c HE11c HE32c HE33c HE80 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(lia) ltac:(lia)), U_SLit in Hcp.
          rewrite (zcanon_id 0) in Hcp by (unfold M64; lia).
          cbn [branch_taken] in Hcp. apply Bool.negb_true_iff in Hcp.
          destruct (Z.eq_dec Jm (nm - Z.of_nat (length Wl))) as [He|He]; [|lia].
          exfalso. replace (nm - (re - rp) - Jm) with 0 in Hcp by lia. vm_compute in Hcp. discriminate. }
        assert (Hjnp : Jm = Z.of_nat (length C) - (p + Z.of_nat (length Wl))) by (unfold Jm in *; unfold rread_k in *; lia).
        assert (Hfill0 : rmread_fill (nm - Z.of_nat (length Wl)) (Z.of_nat (length C)) (p + Z.of_nat (length Wl)) = 0)
          by (unfold rmread_fill; unfold Jm in Hjnp; rewrite Hjnp; unfold SRC_BUFSIZ; lia).
        assert (Hgt : ((nm - Z.of_nat (length Wl)) >? Z.of_nat (length C) - (p + Z.of_nat (length Wl))) = true)
          by (apply Z.gtb_lt; lia).
        rewrite Hgt in Hflm5. rewrite Hfill0, Z.add_0_r in Hrem.
        frd_run RUNF HS0 HJ SHOK.
        { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
          destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
          rewrite ?VB2c in Hr0; apply AWRgen; lia. }
        (* 0x8ef1c - 0x8ef00 wrote only fread's frame *)
        pose proof (fr_kept_of_frame segs _ _ (w_H W5) _ _ ZS5 HFr6
          ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2c in Hrr; unfold ZS5; lia|]);
                destruct Hin)) as U6.
        assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ ZS5 a -> aview segs (w_H W5) (ms_mem ms6) a = aview segs (w_H W5) mem5 a)
          by (intros a Ha Hz; rewrite (U6 a Ha Hz), (U5 a Ha Hz); reflexivity).
        clear U5 U6.
        pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres6 & _ & _ & _).
        assert (FA6 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W5 (ms_mem ms6)) a = mbyte segs (rd W5 mem5) a).
        { intros a Ha. apply (mbyte_of_aview segs). apply UN5; [change SRC_FILE_BLOCK with 1304 in *; lia|].
          unfold ZS5. change SRC_FILE_BLOCK with 1304 in *. lia. }
        assert (BA6 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W5 (ms_mem ms6)) a = mbyte segs (rd W5 mem5) a).
        { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
          pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
          intros a Ha. apply (mbyte_of_aview segs). apply UN5; [lia|]. unfold ZS5.
          unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        assert (EA6 : forall a, asrc_env_addr K a -> mbyte segs (rd W5 (ms_mem ms6)) a = mbyte segs (rd W5 mem5) a).
        { intros a Ha. apply (mbyte_of_aview segs).
          pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
          pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
          unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        assert (OA6 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W5 (ms_mem ms6)) a = mbyte segs (rd W5 mem5) a).
        { intros a Ha. apply (mbyte_of_aview segs).
          pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
          pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
          unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        (* rpos = rend = f + 280: the window is empty (r = 0 on a short read) *)
        assert (Hwin5 : source_window segs (rd W5 mem5) f []).
        { right. exists 0. split; [lia|]. split; [cbn [length Z.of_nat]; unfold SRC_BUFSIZ; lia|].
          split; [rewrite Z.add_0_r; exact Hrpm|]. split; [cbn [length Z.of_nat]; rewrite !Z.add_0_r; exact Hrem|].
          apply garr8_nil. }
        assert (Hunb6 : asource_unbuffered segs K (rd W5 (ms_mem ms6)) f b C (p + Z.of_nat (length Wl) + Jm))
          by exact (asource_unbuffered_frame segs K (rd W5 mem5) (rd W5 (ms_mem ms6)) f b C _ FA6 BA6 EA6 OA6 (conj Hatm Hwin5)).
        assert (Hfl6 : source_flags segs (rd W5 (ms_mem ms6)) f 24).
        { apply (source_flags_frame segs (rd W5 mem5) (rd W5 (ms_mem ms6)) f 24); [|exact Hflm5].
          intros x Hx. apply FA6. change SRC_FILE_BLOCK with 1304 in *. lia. }
        assert (K6 : rread_kept segs B RFREAD_STK lyc Sc W memc W5 (ms_mem ms6) (spZ regs) (rread_wrset f d nm)).
        { apply (frd_kept_extend lyc Sc W memc W5 mem5 md5 (ms_mem ms6) (spZ regs) (rread_wrset f d nm) K45 HAR5).
          - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
          - lia.
          - intros a Ha. apply Hpres0. lia.
          - intros a Ha Hs. apply UN5; [exact Ha|]. unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
          - intros a Ha. apply (fr_apresent_grows _ (ms_mem ms5)); [exact HG6|].
            exact (fr_apresent_grows _ mem5 (ms_mem ms5) a HG5 Ha).
          - intros a Ha. apply Hpres6. lia. }
        assert (BAND6 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
          aview segs (w_H W5) (ms_mem ms6) s = aview segs (w_H W) memc s).
        { intros s Hs. rewrite (UN5 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND45 s Hs)|].
          unfold ZS5. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
          unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        (* the registers at the second __toread call *)
        frd_reg0 HS0 (1%bv : bv 5) V1. frd_reg0 HS0 (2%bv : bv 5) V2.
        frd_reg0 HS0 (3%bv : bv 5) V3. frd_reg0 HS0 (4%bv : bv 5) V4.
        frd_reg0 HS0 (8%bv : bv 5) V8. frd_reg0 HS0 (10%bv : bv 5) V10.
        assert (Rra2 : getr (ms_regs ms6) 1%bv = Z_to_bv 64 (val A_TEXT + 168))
          by (rewrite V1; exact (fr_codeptr_val val _ 168 HEIc)).
        assert (Hspc6 : spZ (ms_regs ms6) = spZ regs - 64).
        { unfold spZ in *. rewrite V2. cbn [sv_denot]. rewrite HE2c. rewrite unsigned_lit_small by lia. lia. }
        assert (Rgp6 : getr (ms_regs ms6) 3%bv = w64 (as_gp B)).
        { rewrite V3. cbn [sv_denot]. rewrite HE3c, Hgp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
        assert (Rtp6 : getr (ms_regs ms6) 4%bv = w64 (as_tp B)).
        { rewrite V4. cbn [sv_denot]. rewrite HE4c, Htp. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
        assert (Ra06 : getr (ms_regs ms6) 10%bv = w64 f).
        { rewrite V10. cbn [sv_denot]. rewrite HE13c. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
        assert (Rs0v6 : getr (ms_regs ms6) 8%bv = w64 f).
        { rewrite V8. cbn [sv_denot]. rewrite HE13c. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
        assert (Rs06 : s0Z (ms_regs ms6) = f)
          by (unfold s0Z; rewrite Rs0v6; unfold w64; apply fa_u64_small; change SRC_FILE_BLOCK with 1304 in *; lia).
        assert (Hret6 : YK0s.ret_ok (getr (ms_regs ms6) 1%bv)).
        { unfold YK0s.ret_ok. rewrite Rra2. unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by exact Hra_rng168.
          rewrite Z.add_0_r. rewrite YK0s.land_m2_even by exact Hra_ev168. reflexivity. }
        (* the second __toread call: F_EOF is set, it returns -1 *)
        lazymatch type of HS0 with st_ok ?sg ?Ev ?ssx (restrict ?HH ?msr) =>
          rewrite (st_ok_restrict_mkst sg HH Ev ssx msr HS0 ltac:(vm_compute; reflexivity));
          replace (ss_pc ssx) with (sigma FS_toread) by (vm_compute; reflexivity) end.
        eapply SRr_bind.
        { apply (frd_call_toread segs B K LAWS segs_low (sigma FS_toread) HTOREAD
                   STK sp0 FP ly S W0 mem0 md0 own lyc Sc W5 (ms_mem ms6) _ k regs (ms_regs ms6) []
                   f b (p + Z.of_nat (length Wl) + Jm) 24 (val A_TEXT + 168) C HJ Hspc6 Hal16 Hstk1 Hsple Rra2
                   Hret6 Hra4096 Rgp6 Rtp6
                   ltac:(apply achain_low; rewrite Rs06; change SRC_FILE_BLOCK with 1304 in *; lia)
                   Ra06 Hblkf Hblkb Hbstk Hunb6 Hfl6 HWRF). }
        intros W7 c7 Hle7 (ly7 & S7 & regs7 & mem7 & md7 & Hcfg7 & HJ7 & HJt7 & HPpres7 & Ht7post).
        subst c7. rewrite Rra2.
        destruct Ht7post as (-> & -> & Ha0t7 & Hunb7 & Hfl7 & Hmd7 & Hrp7 & Hre7 & Hband7).
        pose proof HJt7 as (_ & _ & _ & _ & Hiot7 & _ & _ & _ & G1t7 & _ & _ & _ & _ & _ & _ & _ & _).
        pose proof HJ7 as (HAR7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres7 & _ & _ & _).
        pose proof HJ as (HARc6 & _).
        assert (KST7 : forall a, spZ regs + -64 <= a < spZ regs + 0 ->
          aview segs (w_H W7) mem7 a = aview segs (w_H W5) (ms_mem ms6) a).
        { intros a Ha. apply G1t7.
          - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
          - rewrite Hspc6. lia. }
        assert (KPR7 : forall a, spZ regs + -64 <= a < spZ regs + 0 -> apresent (w_H W7) mem7 a).
        { intros a Ha. apply Hpres7. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        (* reseat at the return 0x8ef04 *)
        lazymatch type of HS0 with st_ok _ ?Ev ?ssc ?msc =>
          let rs := eval vm_compute in (pick (ss_mem ssc) [0%nat]) in
          assert (Hkept7 : Forall (region_kept segs Ev (ms_mem msc) (mrestrict (w_H W7) mem7)) rs)
            by (cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
                apply (frd_region_kept Ev W5 W7 (ms_mem ms6) mem7 2%nat (spZ regs)); [exact VB2c | exact KST7 | exact KPR7]);
          pose proof (fr_after_call segs val 96%nat Ev ssc msc regs7 (mrestrict (w_H W7) mem7) rs 168
            HEIc ltac:(lia) HS0 ltac:(vm_compute; reflexivity) ltac:(cbv; lia)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HPpres7 Hkept7) as HSd;
          let ss7 := eval vm_compute in (ss_after_call ssc rs 96 168) in
          change (ss_after_call ssc rs 96 168) with ss7 in HSd
        end.
        rewrite <- restrict_mkst_fx in HSd.
        clear HS0 Hkept7 V1 V2 V3 V4 V8 V10.
        pose proof (fr_img_env_havoc val _ 96 (map (getr regs7) CLOB) HEIc ltac:(rewrite length_map; cbv; lia)) as HEId.
        pose proof (frd_base_havoc _ 96 (map (getr regs7) CLOB) 2 (spZ regs) ltac:(lia) VB2c) as VB2d.
        pose proof (frd_ew_havoc _ 96 (map (getr regs7) CLOB) 11 _ ltac:(lia) HE11c) as HE11d.
        pose proof (frd_ew_havoc _ 96 (map (getr regs7) CLOB) 12 _ ltac:(lia) HE12c) as HE12d.
        pose proof (frd_ew_havoc _ 96 (map (getr regs7) CLOB) 32 _ ltac:(lia) HE32c) as HE32d.
        pose proof (frd_ew_havoc _ 96 (map (getr regs7) CLOB) 33 _ ltac:(lia) HE33c) as HE33d.
        pose proof (frd_ew_havoc _ 96 (map (getr regs7) CLOB) 80 _ ltac:(lia) HE80) as HE80d.
        lazymatch type of HSd with st_ok_pi _ _ ?E4 _ _ =>
          clear SHOK; assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E4 (mrestrict (w_H W7) mem7)) by apply Forall_nil end.
        rename HSd into HS0. clear HJ. rename HJ7 into HJ.
        (* 0x8ef04 bnez a0: __toread returned -1 (F_EOF) *)
        frd_branch_auto; clear HS0; intros Hk6 HS0.
        { frd_run RUNF HS0 HJ SHOK.
          { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
            destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
            rewrite ?VB2d in Hr0; apply AWRgen; lia. }
          eapply (RETF W7 _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity)).
          intros matR.
          set (ZS7 := fun a => spZ regs - 64 <= a < spZ regs).
          pose proof (fr_kept_of_frame segs _ _ (w_H W7) _ _ ZS7 HFr7
            ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
                  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2d in Hrr; unfold ZS7; lia|]);
                  destruct Hin)) as UN7.
          pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & _ & _ & _).
          frd_reg HS0 (1%bv : bv 5) R1x.
          assert (RF1 : getr (ms_regs ms7) 1 = getr regs 1).
          { rewrite R1x. cbn [sv_denot]. rewrite !ew_havoc_old by lia. rewrite HE1, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
          assert (HPR : aregs_preserved regs (ms_regs ms7)).
          { lazymatch type of HS0 with st_ok_pi _ _ ?Ex ?ss _ =>
              exact (aregs_preserved_of_st_ok segs (w_H W7) Ex (abs_ss val ss) ms7 regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]
                       HS0 (frd_ea_havoc2 _ _ 96 _ (frd_ea_havoc2 _ _ 76 _ (frd_ea_havoc2 _ _ 56 _
                              (frd_ea_havoc val regs _ 36 _ ltac:(lia)) ltac:(lia)) ltac:(lia)) ltac:(lia))
                       ltac:(vm_compute; reflexivity)) end. }
          frd_reg HS0 (10%bv : bv 5) R10x.
          assert (RF10 : getr (ms_regs ms7) 10 = w64 (rread_k nm (Z.of_nat (length C)) p)).
          { rewrite R10x, denot_lit_U.
            rewrite (frd_bs_U_ret _ nm (nm - (re - rp) - Jm) _ HE12d HE11d ltac:(lia)
                      (frd_bs_U_s4k _ nm rp re Jm 80 HE12d HE11d HE32d HE33d HE80d ltac:(lia) ltac:(lia) ltac:(lia)
                         ltac:(lia) ltac:(lia) ltac:(lia))
                      ltac:(lia)).
            unfold w64. f_equal. lia. }
          (* what __toread kept, and what the path kept *)
          assert (K7 : rread_kept segs B RTOREAD_STK lyc Sc W5 (ms_mem ms6) W7 mem7 (spZ (ms_regs ms6))
                         (fun a => f <= a < f + SRC_FILE_BLOCK)).
          { apply (frd_kept_of_acall segs B).
            apply (acall_kept_of_journal segs B segs_low RTOREAD_STK (spZ (ms_regs ms6)) (rtoread_fp f) [] lyc Sc W5
                     (ms_mem ms6) _ lyc Sc W7 mem7 md7 0 (fun a => f <= a < f + SRC_FILE_BLOCK) HJt7 HARc6);
              [| | exact Hcl].
            - intros a (r & Hr & Ha). unfold rtoread_fp in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact Ha.
            - intros bb m i Hb _ _. exact Hb. }
          assert (K67 : rread_kept segs B RFREAD_STK lyc Sc W memc W7 mem7 (spZ regs) (rread_wrset f d nm)).
          { apply (frd_kept_trans segs B RFREAD_STK RTOREAD_STK RFREAD_STK lyc Sc W memc W5 (ms_mem ms6) W7 mem7
                     (spZ regs) (spZ (ms_regs ms6)) (spZ regs) (rread_wrset f d nm) (fun a => f <= a < f + SRC_FILE_BLOCK)
                     (rread_wrset f d nm) K6 K7).
            - lia.
            - lia.
            - rewrite Hspc6. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK. lia.
            - rewrite Hspc6. lia.
            - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
            - lia.
            - intros a Ha. apply Hpres0. lia.
            - intros a Ha. exact Ha.
            - intros a Ha. left. exact Ha. }
          assert (KF : rread_kept segs B RFREAD_STK lyc Sc W memc W7 (ms_mem ms7) (spZ regs) (rread_wrset f d nm)).
          { apply (frd_kept_extend lyc Sc W memc W7 mem7 md7 (ms_mem ms7) (spZ regs) (rread_wrset f d nm) K67 HAR7).
            - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
            - lia.
            - intros a Ha. apply Hpres0. lia.
            - intros a Ha Hs. apply UN7; [exact Ha|]. unfold ZS7. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
            - intros a Ha. exact (fr_apresent_grows _ mem7 (ms_mem ms7) a HG7 Ha).
            - intros a Ha. apply HpresF. lia. }
          (* the delivered bytes: kept by the last run, by __toread and by the runs before it *)
          assert (DKF : forall x, d <= x < d + nm -> aview segs (w_H W7) (ms_mem ms7) x = aview segs (w_H W5) mem5 x).
          { intros x Hx.
            pose proof (proj2 (Hdwr x Hx)) as Hxs.
            assert (Hxr : 0 <= x < 2 ^ 64) by lia.
            transitivity (aview segs (w_H W7) mem7 x).
            { apply UN7; [exact Hxr|]. unfold ZS7. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hxs. lia. }
            transitivity (aview segs (w_H W5) (ms_mem ms6) x).
            { apply (frd_dest_kept RTOREAD_STK lyc Sc W5 (ms_mem ms6) W7 mem7 (spZ (ms_regs ms6))
                       (fun a => f <= a < f + SRC_FILE_BLOCK) d nm K7 Hdat HceilL HhiL); [|exact Hx].
              intros a Ha. pose proof (proj2 (Hdwr a Ha)) as Has. split.
              - change SRC_FILE_BLOCK with 1304 in *. destruct Hdf as [Hdj | Hdj]; lia.
              - rewrite Hspc6. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
            apply UN5; [exact Hxr|]. unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hxs. lia. }
          (* the stream after __toread, the orientation word and the band *)
          assert (FA7 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W7 (ms_mem ms7)) a = mbyte segs (rd W7 mem7) a).
          { intros a Ha. apply (mbyte_of_aview segs). apply UN7; [change SRC_FILE_BLOCK with 1304 in *; lia|].
            unfold ZS7. change SRC_FILE_BLOCK with 1304 in *. lia. }
          assert (BA7 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W7 (ms_mem ms7)) a = mbyte segs (rd W7 mem7) a).
          { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
            pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
            intros a Ha. apply (mbyte_of_aview segs). apply UN7; [lia|]. unfold ZS7.
            unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
          assert (EA7 : forall a, asrc_env_addr K a -> mbyte segs (rd W7 (ms_mem ms7)) a = mbyte segs (rd W7 mem7) a).
          { intros a Ha. apply (mbyte_of_aview segs).
            pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
            pose proof (segs_low a Hi) as Hl. apply UN7; [unfold kLowMemEnd in Hl; lia|]. unfold ZS7.
            unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
          assert (OA7 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W7 (ms_mem ms7)) a = mbyte segs (rd W7 mem7) a).
          { intros a Ha. apply (mbyte_of_aview segs).
            pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
            pose proof (segs_low a Hi) as Hl. apply UN7; [unfold kLowMemEnd in Hl; lia|]. unfold ZS7.
            unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
          assert (HAT : asource_at segs K (rd W7 (ms_mem ms7)) f b C (p + rread_k nm (Z.of_nat (length C)) p)).
          { replace (p + rread_k nm (Z.of_nat (length C)) p) with (p + Z.of_nat (length Wl) + Jm) by lia.
            exact (asource_at_frame segs K (rd W7 mem7) (rd W7 (ms_mem ms7)) f b C _ FA7 BA7 EA7 OA7 (proj1 Hunb7)). }
          assert (HMD7 : source_mode segs (rd W7 (ms_mem ms7)) f U32M1).
          { apply (source_mode_frame segs (rd W7 mem7) (rd W7 (ms_mem ms7)) f U32M1); [|exact Hmd7].
            intros a Ha. apply FA7. change SRC_FILE_BLOCK with 1304 in *. lia. }
          assert (BAND7 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
            aview segs (w_H W7) mem7 s = aview segs (w_H W) memc s)
            by (intros s Hs; rewrite (Hband7 s Hs); exact (BAND6 s Hs)).
          destruct (aos_step_closed _ _ _ Hcl Hiot7) as (Hfd7 & Hfs7 & _ & _).
          assert (Hfds7 : m_fds md7 = m_fds mdc) by (unfold m_fds in *; rewrite Hfd7; exact Hfds5).
          assert (Hfss7 : m_fs md7 = m_fs mdc) by (unfold m_fs in *; rewrite Hfs7; exact Hfss5).
          unfold rread_post_base.
          eexists lyc, Sc, (ms_regs ms7), (ms_mem ms7), _.
          split; [rewrite RF1, (fr_ret_of_ok _ Hra); reflexivity|].
          split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ|].
          split; [exact HPR|].
          split; [exact KF|].
          unfold rfread_post. cbv zeta.
          split; [reflexivity|]. split; [reflexivity|].
          split; [exact RF10|].
          split; [exact (HASM W7 (ms_mem ms7) DKF)|].
          split; [exact HAT|].
          split; [exact HMD7|].
          split; [intros Hz; exfalso; lia|].
          split; [exact Hfds7|]. split; [exact Hfss7|].
          intros s Hs. rewrite (UN7 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND7 s Hs)|].
          unfold ZS7. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
          unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
        exfalso. cbn [branch_taken sv_denot havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB] in Hk6.
        rewrite Ha0t7 in Hk6. vm_compute in Hk6. discriminate. }
      (* s4 = 0: Jm = nm - |Wl|; return nm (0x8ef2c-0x8ef34 with s1 = 1) *)
      assert (Hjn : Jm = nm - Z.of_nat (length Wl)).
      { pose proof Hk5 as Hcp. rewrite !denot_lit_U in Hcp.
        rewrite (frd_bs_U_s4k _ nm rp re Jm 80 HE12c HE11c HE32c HE33c HE80 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(lia) ltac:(lia)), U_SLit in Hcp.
        rewrite (zcanon_id 0) in Hcp by (unfold M64; lia).
        cbn [branch_taken] in Hcp. apply Bool.negb_false_iff in Hcp. apply bv_eqb_eq in Hcp.
        apply (f_equal bv_unsigned) in Hcp. rewrite !unsigned_lit_small in Hcp by lia. lia. }
      frd_run RUNF HS0 HJ SHOK.
      { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
        destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
        rewrite ?VB2c in Hr0; apply AWRgen; lia. }
      eapply (RETF W5 _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity)).
      intros matR.
      pose proof (fr_kept_of_frame segs _ _ (w_H W5) _ _ ZS5 HFr6
        ltac:(intros bb wlo whi a Hin Hrr; vm_compute in Hin;
              repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2c in Hrr; unfold ZS5; lia|]);
              destruct Hin)) as U6.
      assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ ZS5 a -> aview segs (w_H W5) (ms_mem ms6) a = aview segs (w_H W5) mem5 a)
        by (intros a Ha Hz; rewrite (U6 a Ha Hz), (U5 a Ha Hz); reflexivity).
      clear U5 U6.
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & _ & _ & _).
      frd_reg HS0 (1%bv : bv 5) R1x.
      assert (RF1 : getr (ms_regs ms6) 1 = getr regs 1).
      { rewrite R1x. cbn [sv_denot]. rewrite !ew_havoc_old by lia. rewrite HE1, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
      assert (HPR : aregs_preserved regs (ms_regs ms6)).
      { lazymatch type of HS0 with st_ok_pi _ _ ?Ex ?ss _ =>
          exact (aregs_preserved_of_st_ok segs (w_H W5) Ex (abs_ss val ss) ms6 regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]
                   HS0 (frd_ea_havoc2 _ _ 76 _ (frd_ea_havoc2 _ _ 56 _ (frd_ea_havoc val regs _ 36 _ ltac:(lia)) ltac:(lia))
                          ltac:(lia))
                   ltac:(vm_compute; reflexivity)) end. }
      frd_reg HS0 (10%bv : bv 5) R10x.
      assert (RF10 : getr (ms_regs ms6) 10 = w64 (rread_k nm (Z.of_nat (length C)) p)).
      { rewrite R10x. cbn [sv_denot]. rewrite HE12c. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. f_equal. lia. }
      assert (FA5 : forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs (rd W5 (ms_mem ms6)) a = mbyte segs (rd W5 mem5) a).
      { intros a Ha. apply (mbyte_of_aview segs). apply UN5; [change SRC_FILE_BLOCK with 1304 in *; lia|].
        unfold ZS5. change SRC_FILE_BLOCK with 1304 in *. lia. }
      assert (BA5 : forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs (rd W5 (ms_mem ms6)) a = mbyte segs (rd W5 mem5) a).
      { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
        pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
        intros a Ha. apply (mbyte_of_aview segs). apply UN5; [lia|]. unfold ZS5.
        unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      assert (EA5 : forall a, asrc_env_addr K a -> mbyte segs (rd W5 (ms_mem ms6)) a = mbyte segs (rd W5 mem5) a).
      { intros a Ha. apply (mbyte_of_aview segs).
        pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))) as Hi.
        pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
        unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      assert (OA5 : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs (rd W5 (ms_mem ms6)) a = mbyte segs (rd W5 mem5) a).
      { intros a Ha. apply (mbyte_of_aview segs).
        pose proof (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))) as Hi.
        pose proof (segs_low a Hi) as Hl. apply UN5; [unfold kLowMemEnd in Hl; lia|]. unfold ZS5.
        unfold kLowMemEnd in Hl. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia. }
      assert (HAT : asource_at segs K (rd W5 (ms_mem ms6)) f b C (p + rread_k nm (Z.of_nat (length C)) p)).
      { replace (p + rread_k nm (Z.of_nat (length C)) p) with (p + Z.of_nat (length Wl) + Jm) by lia.
        exact (asource_at_frame segs K (rd W5 mem5) (rd W5 (ms_mem ms6)) f b C _ FA5 BA5 EA5 OA5 Hatm). }
      assert (HMD5 : source_mode segs (rd W5 (ms_mem ms6)) f U32M1).
      { apply (source_mode_frame segs (rd W5 mem5) (rd W5 (ms_mem ms6)) f U32M1); [|exact Hmdm5].
        intros a Ha. apply FA5. change SRC_FILE_BLOCK with 1304 in *. lia. }
      assert (KF : rread_kept segs B RFREAD_STK lyc Sc W memc W5 (ms_mem ms6) (spZ regs) (rread_wrset f d nm)).
      { apply (frd_kept_extend lyc Sc W memc W5 mem5 md5 (ms_mem ms6) (spZ regs) (rread_wrset f d nm) K45 HAR5).
        - unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
        - lia.
        - intros a Ha. apply Hpres0. lia.
        - intros a Ha Hs. apply UN5; [exact Ha|]. unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hs. lia.
        - intros a Ha. apply (fr_apresent_grows _ (ms_mem ms5)); [exact HG6|].
          exact (fr_apresent_grows _ mem5 (ms_mem ms5) a HG5 Ha).
        - intros a Ha. apply HpresF. lia. }
      assert (DKF : forall x, d <= x < d + nm -> aview segs (w_H W5) (ms_mem ms6) x = aview segs (w_H W5) mem5 x).
      { intros x Hx. pose proof (proj2 (Hdwr x Hx)) as Hxs. apply UN5; [lia|].
        unfold ZS5. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hxs. lia. }
      unfold rread_post_base.
      eexists lyc, Sc, (ms_regs ms6), (ms_mem ms6), _.
      split; [rewrite RF1, (fr_ret_of_ok _ Hra); reflexivity|].
      split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ|].
      split; [exact HPR|].
      split; [exact KF|].
      unfold rfread_post. cbv zeta.
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact RF10|].
      split; [exact (HASM W5 (ms_mem ms6) DKF)|].
      split; [exact HAT|].
      split; [exact HMD5|].
      split; [intros Hz; exfalso; lia|].
      split; [exact Hfds5|]. split; [exact Hfss5|].
      intros s Hs. rewrite (UN5 s ltac:(unfold kLowMemEnd, kHighShadowEnd in Hs; lia)); [exact (BAND45 s Hs)|].
      unfold ZS5. pose proof (proj1 ASAN_CEIL_range) as Hac. unfold ASAN_CEIL in Hac.
      unfold kLowMemEnd, kHighShadowEnd in *. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *. lia.
  + (* B-full: the window covers the request: copy nm bytes and return nm *)
    frd_run RUNF HS0 HJ SHOK.
    { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
      rewrite ?VB2, ?VB13 in Hr0; apply AWRgen; lia. }
    (* ---- the two branch facts: the window is not empty and covers the request ---- *)
    assert (HLpos : 0 < Z.of_nat (length Wl)).
    { destruct (Nat.eq_dec (length Wl) 0%nat) as [HL0|HL0]; [exfalso|lia].
      pose proof Hc as Hcp. cbn [branch_taken sv_denot] in Hcp. rewrite HE32, HE33 in Hcp.
      unfold w64 in Hcp. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in Hcp.
      assert (Hrr : re = rp) by lia. rewrite Hrr, bv_eqb_refl in Hcp. discriminate. }
    assert (Hwne : Wl <> []) by (intros HH; rewrite HH in HLpos; cbn [length] in HLpos; lia).
    destruct (Hgw Hwne) as (Hrplo & Hgwin).
    change SRC_BUF_OFF with 280 in Hrplo.
    assert (Hrp64 : 0 <= rp < 2 ^ 64) by lia.
    assert (Hre64 : 0 <= re < 2 ^ 64) by lia.
    assert (Hnmle : nm <= Z.of_nat (length Wl)).
    { pose proof Hc2 as Hcp. rewrite branch_ltu_U in Hcp. apply Z.ltb_ge in Hcp.
      rewrite (frd_U_win _ rp re (Z.of_nat (length Wl)) HE32 HE33 Hrp64 Hre64 Hrere ltac:(lia)) in Hcp.
      rewrite (frd_U_total _ nm HE12 HE11 ltac:(lia)) in Hcp. lia. }
    assert (Hdstk : forall a, spZ regs - RFREAD_STK <= a < spZ regs -> ~ (d <= a < d + nm))
      by (intros a Ha Hcon; exact (proj2 (Hdwr a Hcon) Ha)).
    assert (Hdimg : forall a, d <= a < d + nm -> ~ in_img segs a).
    { intros a Ha Hi. pose proof (segs_low a Hi) as Hal'.
      pose proof (proj1 (Hdwr a Ha)) as Hw.
      eapply awr_byte_cases in Hw; [| exact LAWS | exact HJ].
      destruct Hw as (_ & [[Hcc _] | [(_ & bb & mm & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
      - lia.
      - exact (blk_img segs B LAWS lyc Sc W memc mdc bb mm a HAR Hbin Hr Hi).
      - assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
        unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
        exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin' Hr Hi).
      - lia. }
    change SRC_FILE_BLOCK with 1304 in Hdf.
    (* ---- the register file at the memory-copy call ---- *)
    assert (HE2 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 2 = getr regs 2)
      by (rewrite (Eimg_low val _ 2%nat ltac:(cbv [A_TEXT]; lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
    assert (HE3 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 3 = getr regs 3)
      by (rewrite (Eimg_low val _ 3%nat ltac:(cbv [A_TEXT]; lia)); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
    assert (HE4 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 4 = getr regs 4)
      by (rewrite (Eimg_low val _ 4%nat ltac:(cbv [A_TEXT]; lia)); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
    assert (HE10 : ew (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]) 10 = getr regs 10)
      by (rewrite (Eimg_low val _ 10%nat ltac:(cbv [A_TEXT]; lia)); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
    frd_reg_call HS0 (1%bv : bv 5) Rc1.
    frd_reg_call HS0 (2%bv : bv 5) Rc2.
    frd_reg_call HS0 (3%bv : bv 5) Rc3.
    frd_reg_call HS0 (4%bv : bv 5) Rc4.
    frd_reg_call HS0 (10%bv : bv 5) Rc10.
    frd_reg_call HS0 (11%bv : bv 5) Rc11.
    frd_reg_call HS0 (12%bv : bv 5) Rc12.
    assert (HEIc : PaRun.img_env val A_LIMF (EV regs [w64 rp; w64 re; w64 (as_read K); w64 mdv]))
      by assumption.
    assert (Hra136 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + 136))
      by (rewrite Rc1; exact (fr_codeptr_val val _ 136 HEIc)).
    assert (Hspc : spZ (ms_regs ms1) = spZ regs - 64).
    { unfold spZ. rewrite Rc2, denot_SOff, HE2.
      pose proof Hsp44 as A1. pose proof Hsp47 as A2. unfold spZ in A1, A2.
      replace (bv_unsigned (getr regs 2) - 64) with (bv_unsigned (getr regs 2) + -64) by lia.
      apply zcanon_id. unfold M64. lia. }
    assert (Hretok : YK0s.ret_ok (getr (ms_regs ms1) 1)).
    { rewrite Hra136. pose proof HBok as (HB0 & HB1 & HB4).
      apply (fr_v_jalr_lit_even val frd_listing (BASE + 136)); [lia | apply frd_base_even; exact HB4]. }
    assert (Hgpc : getr (ms_regs ms1) 3 = w64 (as_gp B)).
    { rewrite Rc3. cbn [sv_denot]. rewrite HE3, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hgp. }
    assert (Htpc : getr (ms_regs ms1) 4 = w64 (as_tp B)).
    { rewrite Rc4. cbn [sv_denot]. rewrite HE4, Z.add_0_r, Z_to_bv_bv_unsigned. exact Htp. }
    assert (Hc10 : getr (ms_regs ms1) 10 = w64 d).
    { rewrite Rc10. cbn [sv_denot]. rewrite HE10, G10. unfold w64.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (Hc11 : getr (ms_regs ms1) 11 = w64 rp).
    { rewrite Rc11. cbn [sv_denot]. rewrite HE32. unfold w64.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (Hc12 : getr (ms_regs ms1) 12 = w64 nm)
      by (rewrite Rc12; exact (frd_denot_nm2 _ nm HE12 HE11 ltac:(lia))).
    (* ---- what the three runs before the call kept ---- *)
    assert (Hceilsp : alloc_ceiling <= spZ regs - RFREAD_STK)
      by (unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia).
    assert (CLS : kLowShadowBeg = 0x7fff7000) by reflexivity.
    assert (Hdhi47 : d + nm <= 2 ^ 47)
      by (pose proof Hdam as Hdam'; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hdam'; lia).
    set (ZW := fun a => (spZ regs - 64 <= a < spZ regs) \/ (f + 8 <= a < f + 16) \/ (f + 136 <= a < f + 140)).
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZW HFr
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZW; lia|]);
            destruct Hin)) as U0.
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZW HFr0
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZW; lia|]);
            destruct Hin)) as U1.
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZW HFr1
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2, ?VB13 in Hrr; unfold ZW; lia|]);
            destruct Hin)) as U2.
    assert (UN1 : forall a, 0 <= a < 2 ^ 64 -> ~ ZW a ->
              aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
    { intros a Ha Hz. rewrite (U2 a Ha Hz), (U1 a Ha Hz), (U0 a Ha Hz). reflexivity. }
    clear U0 U1 U2.
    assert (HnotFILE : forall s, kLowMemEnd <= s < kHighShadowEnd -> ~ (f <= s < f + 1304)).
    { intros s Hs Hcon. pose proof Hfapp as Hx. unfold in_app in Hx. destruct Hx as (_ & Hx).
      change SRC_FILE_BLOCK with 1304 in Hx. lia. }
    assert (HBAND1 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
              aview segs (w_H W) (ms_mem ms1) s = aview segs (w_H W) memc s).
    { intros s Hs. pose proof (HnotFILE s Hs) as Hnf. apply UN1; [lia|].
      unfold ZW. unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hceilsp. lia. }
    assert (HDESTms1 : rread_dest segs B STK sp0 FP ly S own lyc Sc W (ms_mem ms1)
                         RFREAD_STK (spZ regs) d nm f b (Z.of_nat (length C))).
    { eapply frd_dest_sub;
      [ exact (conj Hdf (conj Hdb (conj Hd0 (conj Hdam (conj Hdat (conj Hdwr (conj Hdra Hdhull)))))))
      | lia | lia | lia | lia | lia | exact HBAND1 ]. }
    (* ---- the call ---- *)
    pose proof (st_ok_restrict_mkst segs (w_H W) _ _ ms1 HS0 ltac:(vm_compute; reflexivity)) as Hshape.
    cbn [ss_pc setpc] in Hshape.
    rewrite Hshape at 1.
    eapply (SRr_bind segs W).
    { eapply frd_call_memcpy_file;
      [ exact LAWS | exact segs_low | exact HMEMCPY | exact HJ | exact Hspc | exact Hal16
      | exact Hstk1 | exact Hsple | exact Hretok | exact Hgpc | exact Htpc
      | exact Hc10 | exact Hc11 | exact Hc12 | lia
      | exact HDESTms1
      | lia | lia | exact Hblkf | lia | lia ]. }
    cbv beta.
    intros W2 c2 Hwl2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10 & Hcpb & Hkeep & Hband2 & Hpres2 & Hsame2).
    rewrite Hra136.
    assert (KEEPav : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + nm) ->
              ~ (spZ regs - 4160 <= a < spZ regs - 64) ->
              aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms1) a).
    { intros a Ha H1 H2. apply Hkeep; [exact Ha | exact H1 | rewrite Hspc; unfold ESTACK; lia]. }
    assert (HfBelow : 0 <= f /\ f + 1304 <= spZ regs - 4224).
    { pose proof Hfceil as X1. pose proof Hceilsp as X2. change SRC_FILE_BLOCK with 1304 in X1.
      unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in X2. lia. }
    (* ---- reseat: keep all three regions, resume at 0x8eee4 ---- *)
    lazymatch type of HS0 with
    | st_ok _ ?Ec ?ssC _ =>
      assert (HSh : st_ok_pi segs val (havoc Ec 36%nat (map (getr regs2) CLOB))
                      (ss_after_call ssC (ss_mem ssC) 36%nat 136)
                      (mkst regs2 (Z_to_bv 64 (BASE + 136)) (mrestrict (w_H W) mem2) (seg_rom segs)));
      [ apply (fr_after_call segs val 36%nat Ec ssC (restrict (w_H W) ms1) regs2
                 (mrestrict (w_H W) mem2) (ss_mem ssC) 136);
        [ assumption
        | lia
        | exact HS0
        | vm_compute; reflexivity
        | cbv [A_TEXT]; lia
        | vm_compute; reflexivity
        | vm_compute; reflexivity
        | vm_compute; reflexivity
        | vm_compute; reflexivity
        | apply submem_refl
        | vm_compute; reflexivity
        | cbn [ms_regs restrict]; exact HP2
        | cbn [ms_mem restrict ss_mem setpc];
          repeat apply Forall_cons; try apply Forall_nil;
          [ apply (frd_region_kept_av Ec (w_H W) (ms_mem ms1) mem2 2%nat (spZ regs));
            [ exact VB2
            | intros a Ha; apply KEEPav;
              [ lia
              | apply Hdstk; unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK; lia
              | lia ]
            | exact Hpres2 ]
          | apply (frd_region_kept_av Ec (w_H W) (ms_mem ms1) mem2 13%nat f);
            [ exact VB13 | intros a Ha; apply KEEPav; lia | exact Hpres2 ]
          | apply (frd_region_kept_av Ec (w_H W) (ms_mem ms1) mem2 13%nat f);
            [ exact VB13 | intros a Ha; apply KEEPav; lia | exact Hpres2 ] ] ]
      | ]
    end.
    rewrite <- restrict_mkst_fx in HSh.
    lazymatch type of HSh with
    | st_ok_pi _ _ ?Eh _ _ =>
      assert (HEIh : PaRun.img_env val A_LIMF Eh)
        by (apply fr_img_env_havoc; [assumption | rewrite length_map; cbv [A_TEXT CLOB]; cbn [length]; lia]);
      assert (SHOKh : sh_ok segs (SLit 0) (@nil shent) Eh (mrestrict (w_H W) mem2)) by apply Forall_nil;
      assert (VB2h : base_val Eh (Some 2%nat) = spZ regs)
        by (cbn [base_val]; rewrite ew_havoc_old by lia; exact VB2);
      assert (VB13h : base_val Eh (Some 13%nat) = f)
        by (cbn [base_val]; rewrite ew_havoc_old by lia; exact VB13);
      assert (HE11h : ew Eh 11 = w64 1) by (rewrite ew_havoc_old by lia; exact HE11);
      assert (HE12h : ew Eh 12 = w64 nm) by (rewrite ew_havoc_old by lia; exact HE12);
      assert (HE32h : ew Eh 32 = w64 rp) by (rewrite ew_havoc_old by lia; exact HE32);
      assert (HE33h : ew Eh 33 = w64 re) by (rewrite ew_havoc_old by lia; exact HE33);
      assert (HE35h : ew Eh 35 = w64 mdv) by (rewrite ew_havoc_old by lia; exact HE35)
    end.
    frd_run RUNF HSh HJ2 SHOKh.
    { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
      rewrite ?VB2h, ?VB13h in Hr0; apply AWRgen; lia. }
    frd_branch_auto; clear HSh; intros Hc3 HSh.
    2:{ exfalso. rewrite branch_eq_U in Hc3.
        rewrite (frd_U_s4 _ nm HE12h HE11h ltac:(lia)) in Hc3.
        rewrite U_SLit in Hc3. rewrite (zcanon_id 0) in Hc3 by (unfold M64; lia).
        cbn in Hc3. discriminate. }
    frd_run RUNF HSh HJ2 SHOKh.
    { intros a (r0 & Hin & Hr0). cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
      rewrite ?VB2h, ?VB13h in Hr0; apply AWRgen; lia. }
    eapply (RETF W _ _ _ _ _ HSh eq_refl); [vm_compute; reflexivity|].
    intros matR.
    (* ---- what the two runs after the call kept ---- *)
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZW HFr2
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2h, ?VB13h in Hrr; unfold ZW; lia|]);
            destruct Hin)) as U3.
    pose proof (fr_kept_of_frame segs _ _ (w_H W) _ _ ZW HFr3
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; rewrite ?VB2h, ?VB13h in Hrr; unfold ZW; lia|]);
            destruct Hin)) as U4.
    assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ ZW a ->
              aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem2 a).
    { intros a Ha Hz. rewrite (U4 a Ha Hz), (U3 a Ha Hz). reflexivity. }
    clear U3 U4.
    (* ---- memory agreement from the call to the return ---- *)
    assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RFREAD_STK <= a < spZ regs) ->
              ~ rread_wrset f d nm a ->
              aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memc a).
    { intros a Ha Hw Hwr. unfold rread_wrset in Hwr. change SRC_FILE_BLOCK with 1304 in Hwr.
      unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hw.
      assert (HzW : ~ ZW a) by (unfold ZW; lia).
      rewrite (UN2 a Ha HzW), (KEEPav a Ha ltac:(lia) ltac:(lia)). exact (UN1 a Ha HzW). }
    assert (AGimg : forall a, in_img segs a ->
              aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memc a).
    { intros a Hi. pose proof (segs_low a Hi) as Hlo. pose proof (Hdimg a) as Hdi.
      assert (Hnf : ~ (f <= a < f + 1304)).
      { intros Hcon. apply (blk_img segs B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK a HAR Hblkf); [|exact Hi].
        rewrite RQ. change SRC_FILE_BLOCK with 1304. lia. }
      apply AG; [lia | unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK; lia |].
      unfold rread_wrset. change SRC_FILE_BLOCK with 1304. intros [Hx | Hx]; [exact (Hnf Hx) | exact (Hdi Hx Hi)]. }
    assert (APG : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms3) a).
    { intros a Ha. apply (fr_apresent_grows _ (ms_mem ms2)); [exact HG3|].
      apply (fr_apresent_grows _ mem2); [exact HG2|]. apply Hpres2.
      apply (fr_apresent_grows _ (ms_mem ms0)); [exact HG1|].
      apply (fr_apresent_grows _ (ms_mem ms)); [exact HG0|].
      apply (fr_apresent_grows _ memc); [exact HG | exact Ha]. }
    assert (APW : forall a, spZ regs - RFREAD_STK <= a < spZ regs -> apresent (w_H W) (ms_mem ms3) a).
    { intros a Ha. apply APG. apply Hpres0. lia. }
    (* ---- the return address and the callee-saved registers ---- *)
    frd_reg HSh (1%bv : bv 5) R1x.
    assert (R1 : getr (ms_regs ms3) 1 = getr regs 1).
    { rewrite R1x. cbn [sv_denot]. rewrite ew_havoc_old by lia.
      rewrite (Eimg_low val _ 1%nat ltac:(cbv [A_TEXT]; lia)).
      rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
    assert (HPR : aregs_preserved regs (ms_regs ms3)).
    { lazymatch type of HSh with st_ok_pi _ _ ?E ?ss _ =>
        exact (aregs_preserved_of_st_ok segs (w_H W) E (abs_ss val ss) ms3 regs
                 [w64 rp; w64 re; w64 (as_read K); w64 mdv]
                 HSh (frd_env_agree_havoc val regs _ _) ltac:(vm_compute; reflexivity)) end. }
    unfold rread_post_base.
    eexists lyc, Sc, (ms_regs ms3), (ms_mem ms3), _.
    split; [rewrite R1, (fr_ret_of_ok _ Hra); reflexivity|].
    split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ2|].
    split; [exact HPR|].
    split.
    { eapply frd_kept_of_agree_all;
      [exact LAWS | exact HAR | exact Hceilsp | exact AG | exact AGimg | exact APG | exact APW]. }
    (* ---- rfread_post ---- *)
    assert (Hrk : rread_k nm (Z.of_nat (length C)) p = nm) by (unfold rread_k; lia).
    lazymatch type of HSh with st_ok_pi _ _ ?E ?ss ?ms =>
      pose proof (st_ok_mem_ok segs E (abs_ss val ss) ms HSh) as (_ & HRS & _) end.
    cbn [ss_mem abs_ss setpc ms_mem restrict] in HRS.
    pose proof (Forall_inv (Forall_inv_tail HRS)) as HR1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HRS))) as HR2.
    destruct HR1 as (_ & _ & _ & HC1). destruct HR2 as (_ & _ & _ & HC2c).
    cbn [YP09.r_base YP09.r_chunks] in HC1, HC2c. rewrite VB13h in HC1, HC2c.
    pose proof (Forall_inv HC1) as CK8.
    pose proof (Forall_inv (Forall_inv_tail HC1)) as CK16.
    pose proof (Forall_inv HC2c) as CK136.
    assert (N8 : val_mem segs (rd W (ms_mem ms3)) (f + 8) 8 (rp + nm)).
    { apply (val_of_chunk_ok segs _ _ _ 8 8%N _ (rp + nm) CK8);
      [ exact (frd_denot_rp_nm _ rp nm HE32h HE12h HE11h ltac:(lia) ltac:(lia) ltac:(lia)) | cbn; lia | cbn; lia ]. }
    assert (N16 : val_mem segs (rd W (ms_mem ms3)) (f + 16) 8 re).
    { apply (val_of_chunk_ok segs _ _ _ 16 8%N (SOff 33 0) re CK16);
      [cbn [sv_denot]; rewrite HE33h; unfold w64; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
    assert (N136 : val_mem segs (rd W (ms_mem ms3)) (f + 136) 4 U32M1).
    { apply (frd_chunk_val4 _ _ _ _ _ CK136). intros i Hi.
      cbn [sv_denot]. rewrite HE35h.
      destruct Hmdcase as [-> | ->]; unfold U32M1;
      (assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia);
      destruct Hi' as [-> | [-> | [-> | ->]]]; apply bv_eq; vm_compute; reflexivity. }
    assert (FAv : forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 8 <= a < f + 16) -> ~ (f + 136 <= a < f + 140) ->
              aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memc a).
    { intros a Ha H1 H2. change SRC_FILE_BLOCK with 1304 in *.
      unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in Hceilsp.
      assert (HzW : ~ ZW a) by (unfold ZW; lia).
      rewrite (UN2 a ltac:(lia) HzW), (KEEPav a ltac:(lia) ltac:(lia) ltac:(lia)). exact (UN1 a ltac:(lia) HzW). }
    assert (FA : forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 8 <= a < f + 16) -> ~ (f + 136 <= a < f + 140) ->
              mbyte segs (rd W (ms_mem ms3)) a = mbyte segs (rd W memc) a)
      by (intros a Ha H1 H2; apply (mbyte_of_aview segs); apply FAv; assumption).
    assert (BA : forall a, b <= a < b + Z.of_nat (length C) ->
              mbyte segs (rd W (ms_mem ms3)) a = mbyte segs (rd W memc) a).
    { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hblkb) as (_ & Hb0 & Hbc & _).
      pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as Hreq.
      intros a Ha. apply (mbyte_of_aview segs).
      apply AG; [lia | unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK in *; lia |].
      unfold rread_wrset. change SRC_FILE_BLOCK with 1304 in *. lia. }
    assert (EA : forall a, asrc_env_addr K a -> mbyte segs (rd W (ms_mem ms3)) a = mbyte segs (rd W memc) a).
    { intros a Ha. apply (mbyte_of_aview segs). apply AGimg.
      apply (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold asrc_env_addr, PSourceMeta.asrc_env_addr in *; lia))). }
    assert (OA : forall a, as_ofl_head K <= a < as_ofl_head K + 8 ->
              mbyte segs (rd W (ms_mem ms3)) a = mbyte segs (rd W memc) a).
    { intros a Ha. apply (mbyte_of_aview segs). apply AGimg.
      apply (proj1 (asil_env _ _ _ _ ASIL a ltac:(unfold PSourceMeta.asrc_env_addr, as_ofl_head in *; lia))). }
    assert (HAW : asource_at_w segs K (rd W memc) f b C p Wl)
      by (apply (asource_at_w_build segs K (rd W memc) f b C p cpos fl mdv Wl); assumption).
    assert (GW : garr8 segs (rd W (ms_mem ms3)) (rp + nm) (skipn (Z.to_nat nm) Wl)).
    { pose proof (frd_garr8_skipn (rd W memc) rp Wl (Z.to_nat nm) ltac:(lia) Hgwin) as G0.
      rewrite Z2Nat.id in G0 by lia.
      apply (garr8_frame segs (rd W memc) (rd W (ms_mem ms3)) (rp + nm) _ G0).
      intros a Ha. rewrite length_skipn in Ha.
      apply FA; [change SRC_FILE_BLOCK with 1304 in *; lia | lia | lia]. }
    unfold rfread_post. cbv zeta. rewrite Hrk.
    split; [reflexivity|]. split; [reflexivity|].
    (* a0 = nm *)
    split.
    { frd_reg HSh (10%bv : bv 5) R10x. rewrite R10x. cbn [sv_denot].
      rewrite ew_havoc_old by lia.
      rewrite (Eimg_low val _ 12%nat ltac:(cbv [A_TEXT]; lia)), (ew_Ereg_nat regs _ 12 12%bv eq_refl), G12.
      unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    (* the delivered bytes: the window prefix, copied to d *)
    split.
    { rewrite (frd_firstn_window C Wl p cpos nm HWl ltac:(lia)).
      apply (frd_garr8_copy (rd W memc) (rd W (ms_mem ms3)) rp d Wl (Z.to_nat nm) Hgwin ltac:(lia)).
      intros i Hi. apply frd_mbyte_of_aview2.
      assert (Hi' : 0 <= i < nm) by lia.
      assert (Hz1 : ~ ZW (d + i)).
      { unfold ZW. intros [Hz | [Hz | Hz]].
        - apply (Hdstk (d + i)); [unfold RFREAD_STK, RTOREAD_STK, RMREAD_STK, ESTACK; lia | lia].
        - lia.
        - lia. }
      assert (Hz2 : ~ ZW (rp + i)) by (unfold ZW; change SRC_FILE_BLOCK with 1304 in *; lia).
      rewrite (UN2 (d + i) ltac:(lia) Hz1), (Hcpb i Hi'), (UN1 (rp + i) ltac:(lia) Hz2). reflexivity. }
    (* the stream at p + nm, the window drained by nm *)
    split.
    { apply (asource_at_drain segs K (rd W memc) (rd W (ms_mem ms3)) f b C p Wl nm U32M1 HAW ltac:(lia)).
      - right. exists (rp + nm - f - SRC_BUF_OFF).
        change SRC_BUF_OFF with 280. change SRC_BUFSIZ with 1024.
        replace (f + 280 + (rp + nm - f - 280)) with (rp + nm) by lia.
        rewrite length_skipn.
        replace (rp + nm + Z.of_nat (length Wl - Z.to_nat nm)) with re by lia.
        split; [lia|]. split; [change SRC_FILE_BLOCK with 1304 in *; lia|].
        split; [exact N8|]. split; [exact N16 | exact GW].
      - exact FA.
      - split; [exact N136 | right; reflexivity].
      - exact BA.
      - exact EA.
      - exact OA. }
    split; [split; [exact N136 | right; reflexivity]|].
    (* nm = 0: rpos is rewritten with its own value *)
    split.
    { intros Hnm0 a Ha Hn.
      destruct (Z_lt_le_dec a (f + 16)) as [Hl | Hl]; [destruct (Z_lt_le_dec a (f + 8)) as [Hl2 | Hl2]|].
      - apply FAv; [exact Ha | lia | exact Hn].
      - rewrite Hnm0, Z.add_0_r in N8.
        apply (fr_val_mem_aview_eq (w_H W) memc (ms_mem ms3) (f + 8) 8 rp M8 N8). cbn. lia.
      - apply FAv; [exact Ha | lia | exact Hn]. }
    split; [unfold same_but_materialized in Hsame2; rewrite Hsame2; reflexivity|].
    split; [unfold same_but_materialized in Hsame2; rewrite Hsame2; reflexivity|].
    eapply frd_band_of_agree with (sp := spZ regs) (RSTK := RFREAD_STK) (f := f) (d := d) (l := nm);
      [exact LAWS | exact HAR | exact Hblkf | exact Hdam | exact Hceilsp | exact AG].
Qed.

End walk.

(* ---------------------------------------------------------------------- *)
(* The image-free half of the instances: the value map frd_val (the entry *)
(* pc at A_TEXT), the symbol map frd_sigma (the two callee entries) and   *)
(* frd_val's base facts. Each image's code table, listing certificate and *)
(* instance are in lib/A/Stdio/PFreadMWA.v (asan) and                     *)
(* lib/B/Stdio/PFreadMWB.v (asan-ubsan).                                  *)
(* ---------------------------------------------------------------------- *)
Definition frd_val (pc : Z) (n : nat) : Z := if Nat.eqb n A_TEXT then pc else 0.
Definition frd_sigma (pmc ptr : Z) (s : fsym) : Z := match s with FS_memcpy => pmc | FS_toread => ptr end.

Lemma frd_val_ok : forall pc, 0 <= pc /\ pc + 2 ^ 40 < 2 ^ 64 /\ pc mod 4 = 0 ->
  (0 <= frd_val pc A_TEXT /\ frd_val pc A_TEXT + 2 ^ 40 < 2 ^ 64 /\ frd_val pc A_TEXT mod 4 = 0) /\
  (forall a, 0 <= frd_val pc a < 2 ^ 64).
Proof.
intros pc Hpc. unfold frd_val. split; [cbn; exact Hpc|].
intros a. destruct (Nat.eqb a A_TEXT); lia.
Qed.
