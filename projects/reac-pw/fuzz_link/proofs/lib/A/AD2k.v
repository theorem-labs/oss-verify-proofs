(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2k.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
(* ADAPTED by Theorem Labs, 2026-10 (a Theorem Labs lane), beyond relocation. Donor = cgif A/AD2k.v at
   origin/ossv/recipes c8557374ad2e; "donor :N" is a donor line, ":N" a line of this file.
   1. RESTATED over pcap's read SOURCE (porter ruling 2), as lib/A/AD1u.v is. Donor :112-115 concludes cgif's
      three sink conjuncts (ameta_inv / astdio_env over tfib_K, head 0 at A_ofl_head); :151 concludes AD1u.v:114
      FINV at ly0, i.e. the same three conjuncts over pcap_KS (asrc_meta_inv / asrc_stdio_env / head 0 at
      as_ofl_head pcap_KS), so lib/A/AD1p.v:111 applies it exactly as donor AD1p.v:102 does. The donor's
      Require of AE2k (donor :17) becomes Stdio/PSource PSourceMeta PSourceK and AD1u (:47-48).
   2. finv_check (donor :25-32, :57-68). cgif's path 0x20e00 (13 B), write mode 0x20e60 (3 B) and trailer
      0x20ea0 (2 B) have no pcap counterpart and go; the two image strings pcap_KS names are read from the
      image as the donor reads its own: "rb\0" at as_mode = 0x20d40 (3 B; key (b) .rodata+0x10a60, image
      bytes 72 62 00) and musl's "rwa\0" at as_rwa = 0x20026 (4 B; key (b) .rodata+0xfd46, bytes 72 77 61 00).
      The .bss cells, key (a) from the unstripped twin's symtab (36da3052c383...): threaded = __libc+1 =
      0x651ea1, need_locks = __libc+3 = 0x651ea3, ofl_lock+0 = 0x652300 (4 B), ofl_head+0 = 0x652308 (8 B),
      canary = __stack_chk_guard+0 = 0x651c50, meta ptr = _ZL24interceptor_metadata_map+0 = 0xa9c80 holding
      _ZZL28InitializeCommonInterceptorsvE12metadata_mem+0 = 0xa9c88 (values: Stdio/PSourceK.v:66-80). As in
      the donor, finv_check_all reads them in the start-up certificate's 50 hand-off states (lib/A/AB01.v
      HS_tfib_list), not in file bytes. KRange (EVar 254) lower bound 1531 -> 1527 = pcap_img_end / 4096
      (AD1g.v:89).
   3. The stdio step (donor :159-170, :196-208) proves pcap's six asrc_stdio_env conjuncts (Stdio/PSource.v:
      218-231) in place of cgif's eight: no path, write-mode or trailer step; the mode step reads "rb\0"
      (src_mode_Z) at 134464 and the rwa step reads "rwa\0" (src_modeset_Z) at 131110.
   4. The image end is pcap_img_end (Reusable/PcapImgEnd.v) where the donor writes 0x5fb000 (donor :82, :118),
      and tfib_rom_all (AB13.v:148) is stated over it, so the three numeric lia steps that cross it
      (finv_img_byte :113, finv_img_range :125-126, the meta-region bound :183) unfold pcap_img_end and
      YImgTop.IMG_TOP first. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB12 AB1h AB13 AB01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD1g AD2i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0d YI04 YI00 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
(* RESTATED over pcap's read SOURCE (porter ruling 2), exactly as lib/A/AD1u.v is: cgif's AE2k (asink_syms tfib_K)
   has no counterpart in fuzz_pcap's image, so the hand-off state is checked against pcap_KS (Stdio/PSourceK.v)
   and the conclusion is AD1u.v's FINV. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require LinkEntryW.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD1u.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState}.
Section e.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Context {rc : YM05.RunCeil}.
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation m1 := (mrestrict (AD2i.H1 sp rdraw inp ch E model) FULL).
#[local] Notation u := (uE E).
Let MRm1 := AD2i.mbyte_MR_m1 sp rdraw inp Hsp Hva ch E FULL model.
Lemma finv_read_val : forall a n v, kn_read TSEGS ch (ELit 0) a n = Some v -> 0 <= a ->
val_mem tfibsegs m1 a n (u v).
Proof.
intros a n v Hr Ha k Hk.
pose proof (ho_read_byte TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC (ELit 0) a n v Hr k Hk) as X.
rewrite uE_litv in X by lia. rewrite Z.add_0_l in X.
destruct (AD2i.hreader_mbyte sp rdraw inp ch E FULL model _ _ X) as (b & Hb & Hbu).
change tfibsegs with TSEGS. rewrite (MRm1 _ _ Hb). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hbu.
pose proof (ho_read_bound TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ _ _ Hr) as Hv. fold (u v) in Hv.
unfold YO0f.le_byte. rewrite (Z.mod_small (u v)) by exact Hv. rewrite Z.shiftr_div_pow2 by lia.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma finv_img_byte : forall a len, kn_img ch a len = true -> forall i, a <= i < a + len -> 65536 <= a -> a + len <= 6635520 ->
mbyte tfibsegs m1 i = seg_rom tfibsegs (Z_to_bv 64 i) /\ seg_rom tfibsegs (Z_to_bv 64 i) <> None.
Proof.
intros a len H i Hi Hlo Hhi. unfold kn_img in H. apply existsb_exists in H as (K & HK & HKb).
destruct K as [| | |lo hi| | | | | |]; try discriminate HKb. apply andb_prop in HKb as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ HK) as (_ & _ & Hnone).
pose proof (Hnone i ltac:(lia)) as X.
pose proof (tfib_rom_all i ltac:(unfold pcap_img_end, YImgTop.IMG_TOP; lia)) as Hrom. change AB1v.tfibsegs with tfibsegs in Hrom.
split; [|exact Hrom].
destruct (seg_rom tfibsegs (Z_to_bv 64 i)) as [b|] eqn:Hs; [|exfalso; exact (Hrom eq_refl)].
change tfibsegs with TSEGS. apply MRm1. unfold mbyte. rewrite X. exact Hs.
Qed.
Lemma finv_img_range : forall a, in_img tfibsegs a -> 0x10000 <= a < pcap_img_end.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. unfold pcap_img_end, YImgTop.IMG_TOP.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma finv_img_garr8 : forall a (l : list Z), kn_img ch a (Z.of_nat (length l)) = true -> 65536 <= a -> a + Z.of_nat (length l) <= 6635520 ->
(forall j, (j < length l)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat j)) = Some (Z_to_bv 8 (nth j l 0))) ->
Forall (fun b => 0 <= b < 256) l ->
garr8 tfibsegs m1 a l.
Proof.
intros a l Hk Hlo Hhi Hrom Hb j Hj. split; [| exact (proj1 (Forall_forall _ _) Hb _ (nth_In l 0 Hj))].
intros k Hk1. destruct k; [|cbn in Hk1; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (finv_img_byte a (Z.of_nat (length l)) Hk (a + Z.of_nat j) ltac:(lia) Hlo Hhi) as [-> _].
rewrite (Hrom j Hj). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
pose proof (proj1 (Forall_forall _ _) Hb _ (nth_In l 0 Hj)) as Rb.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
cbn beta in Rb. rewrite !(Z.mod_small (nth j l 0) 256) by lia. reflexivity.
Qed.
Lemma finv_img_val : forall a n v, kn_img ch a (Z.of_nat n) = true -> 65536 <= a -> a + Z.of_nat n <= 6635520 ->
(forall k, (k < n)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v n k))) ->
val_mem tfibsegs m1 a n v.
Proof.
intros a n v Hk Hlo Hhi Hrom k Hk1.
destruct (finv_img_byte a (Z.of_nat n) Hk (a + Z.of_nat k) ltac:(lia) Hlo Hhi) as [-> _]. exact (Hrom k Hk1).
Qed.
(* Donor AD2k.v:112-115 states the three conjuncts of cgif's sink hand-off; the same three over pcap's SOURCE
   are exactly lib/A/AD1u.v:114 FINV (asrc_meta_inv / asrc_stdio_env / head 0 over pcap_KS), so the theorem is
   stated as FINV itself and the driver needs no bridging lemma. *)
Theorem tfib_finv_handoff : FINV [] (AD2i.H1 sp rdraw inp ch E model) FULL.
Proof.
destruct (LinkEntryW.lw_handoff sp rdraw brk inp Hsp Hva h (in_fs inp) ch E R FULL model Hch HC) as (HG & Henv & Hnul).
split; [exact HG|]. split; [exact Henv|]. split; [exact Hnul|]. intros f [].
Qed.
End e.
End c.
