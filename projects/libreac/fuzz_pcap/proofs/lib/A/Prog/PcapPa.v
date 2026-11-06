(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v for libreac/fuzz_pcap's program walk: one listing (pcap_listing over psym), fuzz_pcap.asan's (v1.9.0) image range 0x10000..pcap_img_end (Reusable/PcapImgEnd.v, 0x5f7000, checked against the image by lib/A/PcapImgEndCheck.v) and 17 objects, and pa_xcalls in place of PAImg2, fixing the addresses of the program functions the listing calls; module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSyms PcapList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 512.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable psym) := mkPAListing {
pl_tpi : ptree psym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition pcap_tpi : ptree psym := ptree_of_list pcap_listing.
Definition pcap_tw : ctable := Eval vm_compute in (tw_of 0 pcap_listing).
#[global] Instance PL_pcap : PAListing pcap_listing :=
{| pl_tpi := pcap_tpi; pl_tpi_eq := eq_refl; pl_tw := pcap_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base. *)
Definition pcap_xcalls : list (psym * Z) :=
[ (PS_libreac_fuzz_fopen, AF_libreac_fuzz_fopen);
(PS_pcap_source_open, AF_pcap_source_open);
(PS_pcap_source_next, AF_pcap_source_next);
(PS_pcap_source_close, AF_pcap_source_close) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable psym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : psym -> Z;
pa_cert : pi_check psym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> 0x10000 <= a < pcap_img_end;
pa_img_cover : forall ly S md, ALedger pa_segs ly S md -> fst (ly_img ly) <= 0x10000 /\ pcap_img_end <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 17)%nat -> 0x10000 <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= pcap_img_end;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) pcap_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable psym} {PI : PAImg L}.
Lemma pa_fetch_ok : forall pc w, clookup pa_tbl pc = Some w -> fetch_word pa_segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Proof. intros pc w H. exact (pa_tbl_ok pc w H). Qed.
Definition Eimg (E : env) : env :=
{| ew := fun n => if ((A_TEXT <=? n) && (n <? A_LIM))%nat then Z_to_bv 64 (pa_val n) else ew E n; ed := ed E |}.
Lemma Eimg_env : forall E, img_env pa_val A_LIM (Eimg E).
Proof.
intros E a [H1 H2]. cbn [Eimg ew]. replace ((A_TEXT <=? a) && (a <? A_LIM))%nat%bool with true.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. pose proof (pa_val_range a). change (bv_modulus 64) with (2 ^ 64). lia.
- symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia].
Qed.
Lemma Eimg_low : forall E n, (n < A_TEXT)%nat -> ew (Eimg E) n = ew E n.
Proof. intros E n Hn. cbn [Eimg ew]. replace (A_TEXT <=? n)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity. Qed.
Lemma Eimg_img : forall E n, (A_TEXT <= n < A_LIM)%nat -> ew (Eimg E) n = Z_to_bv 64 (pa_val n).
Proof.
intros E n [H1 H2]. cbn [Eimg ew]. replace ((A_TEXT <=? n) && (n <? A_LIM))%nat%bool with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia].
Qed.
Lemma pa_sigma_libreac_fuzz_fopen : pa_sigma PS_libreac_fuzz_fopen = pa_val A_TEXT + AF_libreac_fuzz_fopen.
Proof. apply pa_xcalls. cbn [In pcap_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_pcap_source_open : pa_sigma PS_pcap_source_open = pa_val A_TEXT + AF_pcap_source_open.
Proof. apply pa_xcalls. cbn [In pcap_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_pcap_source_next : pa_sigma PS_pcap_source_next = pa_val A_TEXT + AF_pcap_source_next.
Proof. apply pa_xcalls. cbn [In pcap_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_pcap_source_close : pa_sigma PS_pcap_source_close = pa_val A_TEXT + AF_pcap_source_close.
Proof. apply pa_xcalls. cbn [In pcap_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
