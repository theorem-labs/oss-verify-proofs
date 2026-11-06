From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD2k.v (origin/ossv/recipes c8557374ad2e), with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's asan-ubsan build (pinned image fuzz_pcap.asan-ubsan sha256 9e66f771f22a, symbols from its unstripped twin fuzz_pcap.asan-ubsan sha256 c969d83cdd59). It is the asan-ubsan twin of a Theorem Labs lane's lib/A/AD2k.v (a working branch 9700d736a50): every hunk of that file against the donor's A file is mirrored here, each address re-measured on the asan-ubsan image (keyed by symbol + offset or section + offset, never by a delta from the asan value); a Theorem Labs lane's file restates tfib_finv_handoff over pcap's read SOURCE, carried here with the asan-ubsan values as described in the ADAPTED block below. *)
(* ADAPTED by Theorem Labs, 2026-10, as lib/A/AD2k.v (two Theorem Labs lanes; commit 1ad302a9bfc),
   beyond relocation. Donor = cgif lib/YD2k.v at origin/ossv/recipes c8557374ad2e; "donor :N" is a line of the
   donor's lib/A/AD2k.v (a Theorem Labs lane's numbering), ":N" a line of this file.
   1. RESTATED over pcap's read SOURCE (porter ruling 2), as Reusable/YD1u.v is. Donor :112-115 concludes cgif's
      three sink conjuncts (ameta_inv / astdio_env over tfib_K, head 0 at A_ofl_head); tfib_finv_handoff here
      concludes YD1u.v's FINV at ly0, i.e. the same three conjuncts over the asan-ubsan pcap_KS (lib/B/Stdio/
      PSourceK.v; asrc_meta_inv / asrc_stdio_env / head 0 at as_ofl_head pcap_KS), so Reusable/YD1p.v applies it
      exactly as the donor's YD1p.v does. The donor's Require of YE2k becomes Stdio/PSource PSourceMeta,
      lib/B/Stdio/PSourceK and YD1u.
   2. finv_check (donor :25-32, :57-68). cgif's path, write mode and trailer strings have no pcap counterpart and
      go; the two image strings pcap_KS names are read from the image as the donor reads its own: "rb\0" at
      as_mode = 0x20d40 (3 B; key .rodata+0x10a60, bytes 72 62 00 in the asan-ubsan pin 9e66f771f22a) and musl's
      "rwa\0" at as_rwa = 0x20026 (4 B; key .rodata+0xfd46, bytes 72 77 61 00). The .bss cells, keyed by symbol
      in the asan-ubsan unstripped twin's .symtab (c969d83cdd59): threaded = __libc+1 = 0x5f4a21, need_locks =
      __libc+3 = 0x5f4a23 (__libc 0x5f4a20, size 104), ofl_lock+0 = 0x5f4e80 (4 B), ofl_head+0 = 0x5f4e88 (8 B),
      canary = __stack_chk_guard+0 = 0x5f47d0, meta ptr = _ZL24interceptor_metadata_map+0 = 0xa1000 holding
      _ZZL28InitializeCommonInterceptorsvE12metadata_mem+0 = 0xa1008 (= lib/B/Stdio/PSourceK.v's values). As in
      the donor, finv_check_all reads them in the start-up certificate's hand-off states (Reusable/YB01.v
      HS_tfib_list), not in file bytes. KRange (EVar 254) lower bound 1531 -> 1527 = pcap_img_end / 4096
      (0x5f7000 / 4096, the same in both builds).
   3. The stdio step (donor :159-170, :196-208) proves pcap's six asrc_stdio_env conjuncts (Stdio/PSource.v) in
      place of cgif's eight: no path, write-mode or trailer step; the mode step reads "rb\0" (src_mode_Z) at
      134464 = 0x20d40 and the rwa step reads "rwa\0" (src_modeset_Z) at 131110 = 0x20026; the ofl head is
      6246024 = 0x5f4e88.
   4. The image end is pcap_img_end (Reusable/PcapImgEnd.v) where the donor writes 0x5fb000, and tfib_rom_all
      (YB13.v) is stated over it, so the numeric lia steps that cross it (finv_img_byte, finv_img_range, the
      meta-region bound) unfold pcap_img_end and YImgTop.IMG_TOP first. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.libreac.fuzz_pcap.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB12 YB1h YB13 YB01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YF0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD1g YD2i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0d YI04 YI00 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v.
(* RESTATED over pcap's read SOURCE (porter ruling 2), exactly as Reusable/YD1u.v is: cgif's YE2k (asink_syms
   tfib_K) has no counterpart in fuzz_pcap's images, so the hand-off state is checked against the asan-ubsan
   pcap_KS (lib/B/Stdio/PSourceK.v) and the conclusion is YD1u.v's FINV. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD1u.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Definition e254 : expr := EMd M_MUL (ELit 4096) (EVar 254).
Definition finv_check (ch : acs) : bool :=
(match kn_read TSEGS ch (ELit 0) (symaddr Symbols.AsanUbsan.s__ZL24interceptor_metadata_map) 8 with Some v => expr_eqb v (ELit (symaddr Symbols.AsanUbsan.s__ZZL28InitializeCommonInterceptorsvE12metadata_mem)) | _ => false end
&& match kn_read TSEGS ch (ELit 0) (symaddr Symbols.AsanUbsan.s__ZZL28InitializeCommonInterceptorsvE12metadata_mem) 8 with Some v => expr_eqb v e254 | _ => false end
&& kn_mem (KZero (SA e254 0) (ELit 3727360)) ch
&& kn_mem (KRange (EVar 254) 1527 34359735410) ch
(* "rb\0" at as_mode = PCAP_MODE = 0x20d40 (3 B) and "rwa\0" at as_rwa = PCAP_RWA = 0x20026 (4 B): the two
   image strings pcap's asrc_stdio_env names, read out of the image the way the donor reads its four
   (donor AD2k.v:29-30 path 0x20e00 13 / mode 0x20e60 3 / trailer 0x20ea0 2 / rwa 0x20124 4). cgif's path,
   write mode and trailer have no pcap counterpart and are dropped with YE2k. *)
&& kn_img ch (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68192)%Z) 3 && kn_img ch (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xfd46)%Z) 4
&& kn_img ch (symaddr (Symbols.AsanUbsan.s___libc + 0x1)%Z) 1 && kn_img ch (symaddr (Symbols.AsanUbsan.s___libc + 0x3)%Z) 1 && kn_img ch (symaddr Symbols.AsanUbsan.s_ofl_lock) 4 && kn_img ch (symaddr Symbols.AsanUbsan.s_ofl_head) 8
&& match kn_read TSEGS ch (ELit 0) (symaddr Symbols.AsanUbsan.s___stack_chk_guard) 8 with Some _ => true | None => false end)%bool.
Lemma finv_check_all : forallb finv_check HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
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
#[local] Notation m1 := (mrestrict (YD2i.H1 sp rdraw inp ch E model) FULL).
#[local] Notation u := (uE E).
Let CHK : finv_check ch = true := proj1 (forallb_forall _ _) finv_check_all ch (HS_tfib_In h ch Hch).
Let MRm1 := YD2i.mbyte_MR_m1 sp rdraw inp Hsp Hva ch E FULL model.
Lemma finv_read_val : forall a n v, kn_read TSEGS ch (ELit 0) a n = Some v -> 0 <= a ->
val_mem tfibsegs m1 a n (u v).
Proof.
intros a n v Hr Ha k Hk.
pose proof (ho_read_byte TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC (ELit 0) a n v Hr k Hk) as X.
rewrite uE_litv in X by lia. rewrite Z.add_0_l in X.
destruct (YD2i.hreader_mbyte sp rdraw inp ch E FULL model _ _ X) as (b & Hb & Hbu).
change tfibsegs with TSEGS. rewrite (MRm1 _ _ Hb). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hbu.
pose proof (ho_read_bound TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ _ _ Hr) as Hv. fold (u v) in Hv.
unfold YO0f.le_byte. rewrite (Z.mod_small (u v)) by exact Hv. rewrite Z.shiftr_div_pow2 by lia.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma finv_img_byte : forall a len, kn_img ch a len = true -> forall i, a <= i < a + len -> 65536 <= a -> a + len <= (symaddr ImgPages.AsanUbsan.top) ->
mbyte tfibsegs m1 i = seg_rom tfibsegs (Z_to_bv 64 i) /\ seg_rom tfibsegs (Z_to_bv 64 i) <> None.
Proof.
intros a len H i Hi Hlo Hhi. unfold kn_img in H. apply existsb_exists in H as (K & HK & HKb).
destruct K as [| | |lo hi| | | | | |]; try discriminate HKb. apply andb_prop in HKb as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ HK) as (_ & _ & Hnone).
pose proof (Hnone i ltac:(lia)) as X.
pose proof (tfib_rom_all i ltac:(unfold pcap_img_end, YImgTop.IMG_TOP; lia)) as Hrom. change YB1v.tfibsegs with tfibsegs in Hrom.
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
Lemma finv_img_garr8 : forall a (l : list Z), kn_img ch a (Z.of_nat (length l)) = true -> 65536 <= a -> a + Z.of_nat (length l) <= (symaddr ImgPages.AsanUbsan.top) ->
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
Lemma finv_img_val : forall a n v, kn_img ch a (Z.of_nat n) = true -> 65536 <= a -> a + Z.of_nat n <= (symaddr ImgPages.AsanUbsan.top) ->
(forall k, (k < n)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v n k))) ->
val_mem tfibsegs m1 a n v.
Proof.
intros a n v Hk Hlo Hhi Hrom k Hk1.
destruct (finv_img_byte a (Z.of_nat n) Hk (a + Z.of_nat k) ltac:(lia) Hlo Hhi) as [-> _]. exact (Hrom k Hk1).
Qed.
(* Donor AD2k.v:112-115 states the three conjuncts of cgif's sink hand-off; the same three over pcap's SOURCE
   are exactly Reusable/YD1u.v's FINV (asrc_meta_inv / asrc_stdio_env / head 0 over pcap_KS), so the theorem is
   stated as FINV itself and the driver needs no bridging lemma. *)
Theorem tfib_finv_handoff : FINV (YD1g.ly0 ch E model) (YD2i.H1 sp rdraw inp ch E model) FULL.
Proof.
unfold FINV.
pose proof CHK as H. unfold finv_check in H.
apply andb_prop in H as [H Kcan]. apply andb_prop in H as [H Kofh]. apply andb_prop in H as [H Kofl]. apply andb_prop in H as [H Knl].
apply andb_prop in H as [H Kthr]. apply andb_prop in H as [H Krwa]. apply andb_prop in H as [H Kmode].
apply andb_prop in H as [H Krng]. apply andb_prop in H as [H Kzero]. apply andb_prop in H as [Kptr Kmem].
destruct (YD1g.u254 sp rdraw brk inp h ch E R FULL model Hch HC) as [E254 R254]. change YD1g.e254 with e254 in E254, R254.
set (M := u e254) in *.
assert (ZC : forall a n, kn_img ch a (Z.of_nat n) = true -> 65536 <= a -> a + Z.of_nat n <= (symaddr ImgPages.AsanUbsan.top) ->
(forall k, (k < n)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 0)) -> val_mem tfibsegs m1 a n 0).
{ intros a n Hk Hlo Hhi Hz. apply (finv_img_val a n 0 Hk Hlo Hhi). intros k Hkn. rewrite (Hz k Hkn). f_equal. f_equal.
unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
split; [|split].
-
exists M. split; [|split].
+
cbn [YD1g.ly0 ly_extra]. unfold YD1g.extra.
pose proof (YD1g.dm_vals E) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W254 & _). change YD1g.e254 with e254 in W254.
replace (M, AMETA_SIZE) with (wzp (YD1g.d254 E)) by (rewrite W254; reflexivity).
apply in_map. apply filter_In. split.
* destruct (YD1g.vm_shape sp rdraw brk inp h ch E R FULL model Hch HC) as (fog & _ & _ & ->).
apply in_app_iff. right. apply in_app_iff. right. cbn. tauto.
*
destruct (YD1g.known E (YD1g.d254 E)) eqn:Hk; [|reflexivity]. exfalso.
unfold YD1g.known in Hk. apply existsb_exists in Hk as (d & Hd & Heq). apply YD1g.iv_eqb_eq in Heq.
apply (f_equal (fun iv => bv_unsigned (snd iv))) in Heq. unfold YD1g.d254 in Heq. rewrite YD1g.u_snd_dm in Heq by lia.
unfold YD1g.KNOWN in Hd. cbn [In] in Hd.
unfold YD1g.dP, YD1g.dQ, YD1g.dT, YD1g.dF, YD1g.dNB, YD1g.dSB, YD1g.dC, YD1g.dD in Hd.
unfold YD1g.dLow, YD1g.dHigh, YD1g.dGap in Hd.
repeat (destruct Hd as [<- | Hd]; [rewrite YD1g.u_snd_dm in Heq by lia; discriminate Heq|]). exact Hd.
+
intros a Ha. pose proof (finv_img_range a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. subst M. lia.
+
destruct (kn_read TSEGS ch (ELit 0) (symaddr Symbols.AsanUbsan.s__ZL24interceptor_metadata_map) 8) as [vp|] eqn:Hrp; [|discriminate Kptr]. apply expr_eqb_eq in Kptr. subst vp.
destruct (kn_read TSEGS ch (ELit 0) (symaddr Symbols.AsanUbsan.s__ZZL28InitializeCommonInterceptorsvE12metadata_mem) 8) as [vm|] eqn:Hrm; [|discriminate Kmem]. apply expr_eqb_eq in Kmem. subst vm.
pose proof (finv_read_val _ _ _ Hrp ltac:(lia)) as Vp. rewrite uE_litv in Vp by lia.
pose proof (finv_read_val _ _ _ Hrm ltac:(lia)) as Vm. fold M in Vm.
unfold asrc_meta_ok. cbn [as_meta_ptr as_meta_mem pcap_KS]. unfold PCAP_META_PTR, PCAP_META_MEM, AMETA_SIZE.
split; [exact Vp|]. split; [exact Vm|]. split; [lia|]. split; [lia|]. split; [rewrite E254, Z.mul_comm; apply Z_mod_mult|].
intros a Ha.
pose proof (ho_zero_at TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ Kzero (a - M)) as Z0.
unfold elenZ, estart in Z0. cbn [a_base a_off edenot] in Z0. rewrite u64_lit in Z0 by lia. fold (u e254) in Z0. fold M in Z0.
specialize (Z0 ltac:(lia)). replace (M + 0 + (a - M)) with a in Z0 by lia.
change tfibsegs with TSEGS. unfold mbyte. rewrite (YD2i.MR_m1 sp rdraw inp ch E FULL model _ _ Z0). reflexivity.
-
(* Donor AD2k.v:160-168: eight conjuncts (threaded, need_locks, ofl_lock, path, write mode, rwa, trailer,
   canary). pcap's asrc_stdio_env (Stdio/PSource.v:218) has six: no path and no trailer, and its mode cell is
   the read mode "rb\0" at PCAP_MODE, not cgif's "wb\0". *)
unfold asrc_stdio_env. cbn [as_threaded as_need_locks as_ofl_lock as_mode as_rwa as_canary pcap_KS].
unfold PCAP_THREADED, PCAP_NEED_LOCKS, PCAP_OFL_LOCK, PCAP_MODE, PCAP_RWA, PCAP_CANARY.
split; [apply (ZC (symaddr (Symbols.AsanUbsan.s___libc + 0x1)%Z) 1%nat); [exact Kthr | lia | lia | intros k Hk; destruct k as [|k]; [vm_compute; reflexivity | cbn in Hk; lia]]|].
split; [apply (ZC (symaddr (Symbols.AsanUbsan.s___libc + 0x3)%Z) 1%nat); [exact Knl | lia | lia | intros k Hk; destruct k as [|k]; [vm_compute; reflexivity | cbn in Hk; lia]]|].
split; [apply (ZC (symaddr Symbols.AsanUbsan.s_ofl_lock) 4%nat); [exact Kofl | lia | lia | intros k Hk; do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); cbn in Hk; lia]|].
split; [apply (finv_img_garr8 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68192)%Z) (src_mode_Z ++ [0])); [exact Kmode | lia | cbn; lia | intros j Hj; do 3 (destruct j as [|j]; [vm_compute; reflexivity|]); cbn in Hj; lia | apply Forall_forall; intros b Hb; cbn in Hb; repeat (destruct Hb as [<-|Hb]; [lia|]); destruct Hb]|].
split; [apply (finv_img_garr8 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xfd46)%Z) (src_modeset_Z ++ [0])); [exact Krwa | lia | cbn; lia | intros j Hj; do 4 (destruct j as [|j]; [vm_compute; reflexivity|]); cbn in Hj; lia | apply Forall_forall; intros b Hb; cbn in Hb; repeat (destruct Hb as [<-|Hb]; [lia|]); destruct Hb]|].
destruct (kn_read TSEGS ch (ELit 0) (symaddr Symbols.AsanUbsan.s___stack_chk_guard) 8) as [vc|] eqn:Hrc; [|discriminate Kcan].
exists (u vc). split; [apply uE_bound | exact (finv_read_val _ _ _ Hrc ltac:(lia))].
-
replace (as_ofl_head pcap_KS) with (symaddr Symbols.AsanUbsan.s_ofl_head) by reflexivity.
apply (ZC (symaddr Symbols.AsanUbsan.s_ofl_head) 8%nat); [exact Kofh | lia | lia | intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); cbn in Hk; lia].
Qed.
End e.
End c.
