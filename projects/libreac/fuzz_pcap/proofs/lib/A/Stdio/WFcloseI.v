From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fclose at the ASan INTERCEPTOR entry on libreac/fuzz_pcap's v1.9.0 ASan image, for the
   fmemopen READ stream: PFclose.v's afclose_source_spec at IC_ENTRY = __interceptor_trampoline_fclose 0x415cc.

   NOTHING IS RE-WALKED HERE. The interceptor's two machine walks are the relocated donor lemmas of
   lib/A/AE2e.v (cgif_file_fuzzer lib/A/AE2e.v, relocated to pcap by a Theorem Labs lane in a working branch):
     iclose_front   0x415cc -> 0x467a0 ___interceptor_fclose (frame 96), TryAsanInitFromRtl (0x59894), the
                    AddrHashMap metadata pair (0x47b2c acquire / 0x4834c release), up to `jalr a1` at 0x46834,
                    i.e. the pc IC_REAL = 0x8e214 (musl fclose) with ra = IC_RET = 0x46838;
     iclose_tail    0x46838 -> `ret` at 0x468e8, on the path s3 = 0 (no metadata entry for f).
   This file composes them with musl fclose's contract, taken as the ONE callee hypothesis
   afclose_source_spec_musl (proved by a Theorem Labs lane in WFclose.v), in the interface a Theorem Labs lane ruled with
   a working branch a710f30ec77 (PFclose.v's afclose_source_spec_stk / PFCLOSE_MUSL_STK / PFCLOSE_MUSL):
     afclose_source_spec_stk SK segs B K PFCLOSE_MUSL_STK PFCLOSE_MUSL 0x8e2b8 0x8e2c0 rlo rhi.
   The two free return addresses are the SAME at both entries: the frees happen inside musl fclose
   (0x8e2b4 / 0x8e2bc), so the trace prefixes [pc_free_ra0; 0x8e2b8] and [pc_free_ra0; 0x8e2c0] pass through.

   THE STACK. The interceptor runs musl fclose 96 bytes deeper (addi sp,sp,-96 at 0x467a0), so the budget it can
   grant is PFCLOSE_STK - 96 = PFCLOSE_MUSL_STK; afn_pre_at's side condition `STK1 - o <= STK` reads
   16432 + 96 <= 16528 (exactly tight). The journals compose with YC85G.ajournal_sub_tok (the footprint asource_fp f
   carries YI16.sink_token, so the library's ajournal_sub does not apply).

   THE FRONT'S PREMISES, each derived from the statement's own premises:
     cells_hold ic_cells   the four words 0x9b5f0 / 0x9b5f8 (REAL fflush / REAL fclose), 0xa1100 (the metadata
                           map pointer) and 0x103a0 (the hash mask) are all Tfib_const cells (AF0m.v), so AR's
                           am_const pins them (AF0x.tfib_const_lookup); rodata_chk checks them by vm_compute;
     ro_img                from the statement's arodata_okS, chunk by chunk (the port of cgif lib/A/AE24.v:36
                           ffc_ro_img_of_arodata);
     meta_pre              from asrc_meta_inv: the bucket region is all zero, so the AddrHashMap lookup finds no
                           entry (s3 = 0). Every CheckFailed edge of the interceptor is then off the path: the
                           branches 0x4680c / 0x46818 (to the CheckFailed calls 0x46908 / 0x46928) sit behind
                           `beqz s3` at 0x46804, and 0x46874 (to 0x46948) behind `beqz s3` at 0x46838. The
                           symbolic runs decide each branch from these facts: iclose_front's run reaches IC_REAL
                           with RS_running and ra = IC_RET, iclose_tail's run stops only at the final `ret`
                           (SR_jalr). No CheckFailed entry and no __asan_report_* is reached or stepped past.

   SECTION HYPOTHESES (no axiom, no Admitted; AR_laws is not one: YG0q.AR_laws_ok):
     TB                       PcapSyms B: the ASan symbol record's image law (owner a Theorem Labs lane, lib/A/AF0m.v),
                              the hypothesis iclose_front itself carries;
     afclose_source_spec_musl musl fclose's contract (owner a Theorem Labs lane, WFclose.v).
   The symbol record is pcap_KS (PSourceK.v): K = pcap_KS, as a Theorem Labs lane's lemma takes it.

   THE BUILD TREE, by EXACT pushed sha, never "or newer": this file Requires lib/A/AF0m.v and lib/A/AB1v.v,
   which left the branch of e8bb946b7e4 at f63608fbea3 for the branch of d4691bce0fe, so a head of the first at
   or after that one builds this file only together with the second. It is checked in a LOCAL union, never
   pushed, of exactly the members of ONE of these two rows (both built, cb rc=0):
     OLD BASE  a working branch (this branch)
               a working branch  e8bb946b7e4   (carries AF0m / AB1v itself)
               a working branch  410f35f9863
               a working branch  7a2b36f5950
     NEW BASE  a working branch (this branch)
               a working branch  004a9600bc1
               a working branch  d4691bce0fe   (AF0m / AB1v after the move)
               a working branch  410f35f9863
               a working branch  7a2b36f5950
   Every member above is BUILD TREE ONLY: none is merged into this branch.
   One source per statement file (a Theorem Labs lane): lib/A/Stdio's PSource* / PFclose / PFmopsM /
   PFflush and this file come from a working branch; PFmemopenISpec / PFreadISpec / PFmemopenM /
   PFreadM are other owners' and come from a working branch. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YE00 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YE01 YG0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AF0m AF0x AE2y AE3i AE2h AE2e.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require ACeg.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require YC85G.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceK PFclose.
(* The stdio image pcs come from the per-image numerals file (a Theorem Labs lane 02:31Z / 03:54Z). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PStdioImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The return addresses of musl fclose's two free calls (0x8e2b4 / 0x8e2bc), MEASURED (objdump). *)
Definition WFI_FREE1 : Z := (symaddr (Symbols.Asan.s_fclose + 0xa4)%Z).
Definition WFI_JOIN  : Z := (symaddr (Symbols.Asan.s_fclose + 0xac)%Z).

(* ---------------------------------------------------------------------------------------------- *)
(* 1. Small facts.                                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)
(* A return address the caller vouches for (ret_ok) is even: the inverse of YK0s.ret_ok_even. *)
Lemma wfi_ret_ok_even : forall k : word, YK0s.ret_ok k -> bv_unsigned k mod 2 = 0.
Proof.
intros k Hk. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in Hk. rewrite <- Hk. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_0_r.
assert (E : Z.land (bv_unsigned k) (-2) = (bv_unsigned k / 2) * 2).
{ change (-2) with (Z.lnot (Z.ones 1)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
rewrite E. replace (2 ^ 64) with (2 ^ 63 * 2) by reflexivity.
rewrite Z.mul_mod_distr_r by lia. apply Z_mod_mult.
Qed.

Lemma wfi_in_img_of_b : forall a,
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  in_img tfibsegs a.
Proof.
intros a Hb. apply existsb_exists in Hb as (s & Hs & Hc). apply andb_prop in Hc as [H0 H1].
apply Z.leb_le in H0. apply Z.ltb_lt in H1. exists s. split; [exact Hs | lia].
Qed.

(* The last page of the image: any address the meta region must lie above. *)
Lemma wfi_img_top_page : in_img tfibsegs (symaddr (Symbols.Asan.s___pthread_tsd_main + 0x3c8)%Z).
Proof. apply wfi_in_img_of_b. vm_compute. reflexivity. Qed.

(* The read-only segment covers IMG_RO_LO .. IMG_RO_HI. *)
Lemma wfi_seg_ro : exists s, In s tfibsegs /\ seg_writable s = false /\
  Z.of_N (seg_base s) <= IMG_RO_LO /\ IMG_RO_HI <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
assert (Hb : existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? IMG_RO_LO) &&
  (IMG_RO_HI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hc). apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [H0 H1].
exists s. split; [exact Hs|]. split; [destruct (seg_writable s); [discriminate | reflexivity]|].
split; [apply Z.leb_le; exact H1 | apply Z.leb_le; exact H2].
Qed.

Lemma wfi_ro_chunks_unowned :
  forallb (fun c => forallb (fun r => (fst r + snd r <=? YP09.c_off c) || (YP09.c_off c + c_len c <=? fst r))
    Tfib_owned_static) img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wfi_ic_cells_chk : forall ly, rodata_chk ly ic_cells = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Lemma wfi_wvb_io : forall l X (m : Model), m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X m. destruct m. split; reflexivity. Qed.

Lemma wfi_env_low : forall a, asrc_env_addr pcap_KS a -> 0 <= a < 0x7fff8000.
Proof.
intros a Ha. cbv [asrc_env_addr pcap_KS as_threaded as_need_locks as_ofl_lock as_mode as_rwa as_canary
  PCAP_THREADED PCAP_NEED_LOCKS PCAP_OFL_LOCK PCAP_MODE PCAP_RWA PCAP_CANARY] in Ha. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 2. The stream predicate across a change that keeps its bytes. Copied from a Theorem Labs lane's     *)
(*    lib/A/Stdio/WFflush.v (a working branch ad383186b6f): vm_fr, head_env_addr, env_tr,      *)
(*    asource_at_tr. None of them needs the stream's image laws.                                    *)
(* ---------------------------------------------------------------------------------------------- *)
Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable K : asource_syms.

Lemma wfi_vm_fr : forall (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Lemma wfi_head_env_addr : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> asrc_env_addr K a.
Proof. intros a Ha. unfold asrc_env_addr, as_ofl_head in *. lia. Qed.

Lemma wfi_env_tr : forall m m', asrc_stdio_env segs K m ->
  (forall a, asrc_env_addr K a -> mbyte segs m' a = mbyte segs m a) -> asrc_stdio_env segs K m'.
Proof.
intros m m' (E1 & E2 & E3 & E4 & E5 & (cv & Hcv & E6)) Hk. unfold asrc_env_addr in Hk.
split; [eapply wfi_vm_fr; [|exact E1]; intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia|].
split; [eapply wfi_vm_fr; [|exact E2]; intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia|].
split; [eapply wfi_vm_fr; [|exact E3]; intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia|].
split; [eapply garr8_frame; [exact E4|]; intros x Hx; unfold src_mode_Z in Hx; simpl in Hx; apply Hk; lia|].
split; [eapply garr8_frame; [exact E5|]; intros x Hx; unfold src_modeset_Z in Hx; simpl in Hx; apply Hk; lia|].
exists cv. split; [exact Hcv|]. eapply wfi_vm_fr; [|exact E6]. intros x Hx. simpl Z.of_nat in Hx. apply Hk. lia.
Qed.

Ltac vfr HF H :=
  eapply wfi_vm_fr; [|exact H];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; simpl Z.of_nat in Hx;
  unfold SRC_COOKIE_OFF, SRC_BUF_OFF, SRC_BUFSIZ, SRC_FILE_BLOCK in *; apply HF; lia.
Ltac vfr_auto HF :=
  lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
    match goal with H : val_mem _ _ a n v |- _ => vfr HF H end end.

Lemma wfi_asource_at_tr : forall m m' f b C p, asource_at segs K m f b C p ->
  (forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, asrc_env_addr K a -> mbyte segs m' a = mbyte segs m a) ->
  asource_at segs K m' f b C p.
Proof.
intros m m' f b C p (Wn & cpos & fl & mdv & HX) HF Hb He. cbv zeta in HX.
destruct HX as (Hp0 & Hpc & Hcn & Hn63 & Hbw & Hcp & HWd & Hbok & HC & HST & HWIN & HFL & HFL24 & HMD & HCK &
  HENV & HHD & Hfnz).
destruct HST as (S24 & S64 & S72 & S80 & S88 & S96 & Sc8 & Sc16 & Sc24 & Sc32 & S152 & S32 & S40 & S48 & S56 &
  S104 & S112 & S168 & S120 & S140 & S144 & Sf0 & Sf16 & Sb0 & Sdisj).
destruct HFL as [HFL HFLv]. destruct HMD as [HMD HMDv].
exists Wn, cpos, fl, mdv. cbv zeta.
do 8 (split; [assumption|]).
split; [eapply garr8_frame; [exact HC | exact Hb]|].
split.
{ do 21 (split; [vfr_auto HF|]). repeat split; assumption. }
split.
{ destruct HWIN as [(HW0 & H8 & H16) | (i & Hi0 & Hi1 & H8 & H16 & HG)].
  - left. split; [exact HW0|]. split; [vfr HF H8 | vfr HF H16].
  - right. exists i. split; [exact Hi0|]. split; [exact Hi1|].
    split; [vfr HF H8|]. split; [vfr HF H16|].
    eapply garr8_frame; [exact HG|]. intros a Ha. unfold SRC_BUF_OFF, SRC_BUFSIZ, SRC_FILE_BLOCK in *. apply HF. lia. }
split; [split; [vfr HF HFL | exact HFLv]|].
split; [exact HFL24|].
split; [split; [vfr HF HMD | exact HMDv]|].
split; [vfr HF HCK|].
split; [exact (wfi_env_tr m m' HENV He)|].
split; [eapply wfi_vm_fr; [|exact HHD]; intros x Hx; apply He, wfi_head_env_addr; simpl Z.of_nat in Hx; lia|].
exact Hfnz.
Qed.

End T.

(* ---------------------------------------------------------------------------------------------- *)
(* 3. The composition.                                                                              *)
(* ---------------------------------------------------------------------------------------------- *)
Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Variables rlo rhi : Z.
(* The ASan symbol record's image law (owner a Theorem Labs lane, lib/A/AF0m.v): iclose_front's own hypothesis. *)
Hypothesis TB : PcapSyms B.
(* musl fclose's contract at its own entry and budget (owner a Theorem Labs lane, lib/A/Stdio/WFclose.v). *)
Hypothesis afclose_source_spec_musl :
  afclose_source_spec_stk SK tfibsegs B pcap_KS PFCLOSE_MUSL_STK PFCLOSE_MUSL WFI_FREE1 WFI_JOIN rlo rhi.
(* The allocator laws hold of ANY segs and B (YG0q.v:805, no Section hypothesis). *)
Let LAWS : AR_laws tfibsegs B := YG0q.AR_laws_ok tfibsegs B.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* The front's four image words are all Tfib_const cells, so AR's am_const pins them. *)
Lemma wfi_cells_hold_of_chk : forall l ly S (H : word -> bool) mem,
  rodata_chk ly l = true -> ARm B ly S (aview tfibsegs H mem) -> cells_hold (mrestrict H mem) l.
Proof.
intros l ly S H mem Hc HM. unfold rodata_chk in Hc. unfold cells_hold.
rewrite forallb_forall in Hc. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). cbn [fst snd] in Hc |- *. apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
split; [exact H0|]. split; [exact Hhi|].
rewrite forallb_forall in Hcs. apply Forall_forall. intros [[off n] v] Hc'.
specialize (Hcs _ Hc'). cbn [fst snd] in Hcs |- *.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
split; [exact (tfib_const_lookup B TB ly S H mem (base + off) (N.to_nat n) v HM (const_chk_sound _ _ _ _ H1))|].
split; [lia | exact H4].
Qed.

(* The port of cgif lib/A/AE24.v:36 ffc_ro_img_of_arodata: the read-only image chunks are what the statement's
   arodata_okS says they are. Each chunk avoids every owned static (wfi_ro_chunks_unowned) and the errno word. *)
Lemma wfi_ro_img_of_arodata : forall (H : word -> bool) m,
  YE01.arodata_okS tfibsegs B rlo rhi (aview tfibsegs H m) -> ro_img (mrestrict H m).
Proof.
intros H m HRO E. unfold img_ro_region.
split; [cbn; unfold IMG_RO_LO; lia|]. split; [cbn; unfold IMG_RO_HI; lia|]. split; [intros o Ho; cbn in Ho; lia|].
cbn [YP09.r_chunks YP09.r_base base_val]. apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & n & Hv).
pose proof (proj1 (forallb_forall _ _) wfi_ro_chunks_unowned c Hc) as Hown. cbn beta in Hown.
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok c Hc) as Hz. cbn beta in Hz.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hv. subst cv. cbn [YP09.c_off YP09.c_val c_len cv_len] in *. rewrite !Z.add_0_l.
pose proof (YP08.zallb_sound _ _ _ (co + i) Hz ltac:(lia)) as Hb.
unfold img_byte_ok, img_byte in Hb.
assert (Hro : (exists s, In s tfibsegs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= co + i < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (rlo <= co + i < rhi)).
{ left. destruct wfi_seg_ro as (s & Hs & Hw & Hb0 & Hb1). exists s. split; [exact Hs|]. split; [exact Hw|].
  unfold IMG_RO_LO, IMG_RO_HI in *. lia. }
assert (Hns : ~ Exists (in_zr (co + i)) (as_owned_static B)).
{ rewrite (ts_owned B TB). intros HX. apply Exists_exists in HX as (r & Hr & [Hin1 Hin2]). rewrite forallb_forall in Hown.
  specialize (Hown r Hr). cbn beta in Hown. apply Bool.orb_prop in Hown. destruct Hown as [Ho|Ho]; apply Z.leb_le in Ho; lia. }
assert (Hne : ~ (as_errno B <= co + i < as_errno B + 4)) by (rewrite (ts_errno B TB); unfold TFIB_ERRNO; unfold IMG_RO_LO, IMG_RO_HI in *; lia).
pose proof (HRO (co + i) Hro Hns Hne) as Hrd. unfold aview in Hrd.
destruct (seg_rom tfibsegs (Z_to_bv 64 (co + i))) as [b|] eqn:Eb; [|discriminate Hb].
exists b. split; [cbn [cbyte]; unfold img_byte; exact Eb|].
destruct (mbyte tfibsegs (mrestrict H m) (co + i)) as [b'|] eqn:Em; [|discriminate Hrd]. cbn in Hrd. injection Hrd as Hrd.
f_equal. apply bv_eq. exact Hrd.
Qed.

Theorem afclose_source_spec_icpt :
  afclose_source_spec SK tfibsegs B pcap_KS IC_ENTRY WFI_FREE1 WFI_JOIN rlo rhi.
Proof.
unfold afclose_source_spec, afclose_source_spec_stk.
intros W ly S regs mem md ch f b M C p rest HPRE G10 Hperm HSRC Hbuf HMI HRO Hev Hu1 Hu2.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FS : PFCLOSE_STK = 16528) by reflexivity. rewrite FS in Hslo, Hpres, Hstk0, Hbot.
assert (Hsp : 2 ^ 44 <= spZ regs <= 2 ^ 47) by lia.
(* the FILE block and the data buffer are live blocks *)
assert (Hblk : In (f, SRC_FILE_BLOCK) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md f SRC_FILE_BLOCK HAR Hblk) as (Hf16 & Hf0 & Hfceil & _ & _ & _ & _).
assert (RQ : req_size SRC_FILE_BLOCK = SRC_FILE_BLOCK) by reflexivity. rewrite RQ in Hfceil.
destruct (al_blocks _ _ LAWS ly S W mem md b (Z.of_nat (length C)) HAR Hbuf) as (_ & Hb0 & Hbceil & _ & _ & _ & _).
assert (RQb : Z.of_nat (length C) <= req_size (Z.of_nat (length C))) by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length C)) 0); lia).
unfold SRC_FILE_BLOCK in Hfceil.
(* the meta region *)
pose proof HMI as (HX & HMimg & HMptr & HMmem & HM0 & HM47 & HMal & HMZ).
pose proof (HMimg _ wfi_img_top_page) as HMtop.
pose proof (lo_extra ly HLY) as (_ & HEX & _). pose proof (proj1 (Forall_forall _ _) HEX _ HX) as (_ & _ & _ & HMc & _).
cbn [fst snd] in HMc. pose proof (lo_stk_ceil ly HLY) as Hsc.
assert (HAS : AMETA_SIZE = 3727360) by reflexivity.
(* ---- the front: 0x415cc .. the jalr into musl fclose ---- *)
eapply SRr_bind.
{ apply (iclose_front B LAWS TB ly S W regs mem md f M HAR Hal16).
  - unfold IC_STK. lia.
  - exact Hshi.
  - intros a Ha. apply Hpres. unfold IC_STK in Ha. lia.
  - exact G10.
  - lia.
  - lia.
  - exact Hf16.
  - exact (wfi_cells_hold_of_chk ic_cells ly S (w_H W) mem (wfi_ic_cells_chk ly) (proj1 HAR)).
  - exact (wfi_ro_img_of_arodata (w_H W) mem HRO).
  - unfold meta_pre. split; [exact HMmem|]. split; [exact HMZ|].
    split; [match goal with |- ?X <= M => change X with (symaddr ImgPages.Asan.top) end;
            pose proof (Z.div_mod M 4096 ltac:(lia)) as Hd; rewrite HMal in Hd; lia|].
    split; [exact HMal|]. unfold IC_STK. lia. }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & MF1 & HAR1 & R10 & R1 & R2 & R8 & R19 & RK & RSV & AV1 & PRS1 & PM1).
assert (MB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IC_STK <= a < spZ regs) ->
  mbyte tfibsegs (rd W mem1) a = mbyte tfibsegs (rd W mem) a).
{ intros a Ha Hn. apply AE2y.mbyte_of_aview. exact (AV1 a Ha Hn). }
(* ---- the journal of the front: only the 272-byte window below sp0 moved ---- *)
assert (J0 : ajournal (SK:=SK) tfibsegs B PFCLOSE_STK (spZ regs) (asource_fp f) ly S W mem md [] ly S W mem1 md1 0).
{ apply (ajournal_after_write (SK:=SK) tfibsegs B LAWS ACeg.tfib_segs_low PFCLOSE_STK (spZ regs) (asource_fp f)
    ly S W mem md [] ly S W mem md 0 mem1 md1 (fun a => spZ regs - IC_STK <= a < spZ regs) S []
    (ajournal_init (SK:=SK) tfibsegs B PFCLOSE_STK (asource_fp f) ly S W regs mem md ch HPRE)).
  - intros a Ha Hn. exact (AV1 a Ha Hn).
  - exact PM1.
  - exact MF1.
  - intros a Ha. left. unfold awr_byte. left. rewrite FS. unfold IC_STK in Ha. lia.
  - exact HAR1.
  - reflexivity.
  - reflexivity.
  - lia.
  - reflexivity.
  - exact HQT. }
(* ---- musl fclose's precondition at sp0 - 96, budget PFCLOSE_MUSL_STK ---- *)
assert (Esp1 : spZ regs1 = spZ regs + -96).
{ change (spZ regs1) with (bv_unsigned (getr regs1 2)). rewrite R2. unfold YG0d.w64.
  rewrite unsigned_lit_small by (unfold IC_FRAME; lia). unfold IC_FRAME. lia. }
assert (P1 : afn_pre tfibsegs B PFCLOSE_MUSL_STK ly S W regs1 mem1 md1 []).
{ apply (afn_pre_at (SK:=SK) tfibsegs B PFCLOSE_STK (spZ regs) (asource_fp f) ly S W mem md [] ly S W mem1 md1 0
    regs1 PFCLOSE_MUSL_STK (-96) [] J0).
  - exact Esp1.
  - reflexivity.
  - lia.
  - unfold PFCLOSE_MUSL_STK, PFCLOSE_STK. lia.
  - unfold PFCLOSE_MUSL_STK, PFCLOSE_STK. lia.
  - rewrite R1. apply ret_ok_lit; unfold IC_RET; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold YG0d.w64. rewrite unsigned_lit_small by (unfold IC_RET; lia). unfold IC_RET. lia.
  - etransitivity; [exact (RK 3 ltac:(unfold KEPTC; cbn; lia)) | exact Hgp].
  - etransitivity; [exact (RK 4 ltac:(unfold KEPTC; cbn; lia)) | exact Htp].
  - unfold achain. left. split; [|reflexivity]. left. unfold s0Z. rewrite R8. unfold YG0d.w64.
    rewrite unsigned_lit_small by lia. lia. }
(* the stream, the meta region and the read-only words, carried across the front *)
assert (HSRC1 : asource_at tfibsegs pcap_KS (rd W mem1) f b C p).
{ apply (wfi_asource_at_tr tfibsegs pcap_KS (rd W mem) (rd W mem1) f b C p HSRC).
  - intros a Ha. apply MB1; unfold SRC_FILE_BLOCK, IC_STK in *; lia.
  - intros a Ha. apply MB1; unfold IC_STK; lia.
  - intros a Ha. pose proof (wfi_env_low a Ha). apply MB1; unfold IC_STK; lia. }
assert (HMI1 : asrc_meta_inv tfibsegs pcap_KS ly (rd W mem1) M).
{ split; [exact HX|]. split; [exact HMimg|]. split.
  { apply (AF0x.val_mem_ext (rd W mem)); [|exact HMptr]. intros k Hk. apply MB1;
    cbv [as_meta_ptr pcap_KS PCAP_META_PTR]; unfold IC_STK; lia. }
  split.
  { apply (AF0x.val_mem_ext (rd W mem)); [|exact HMmem]. intros k Hk. apply MB1;
    cbv [as_meta_mem pcap_KS PCAP_META_MEM]; unfold IC_STK; lia. }
  split; [exact HM0|]. split; [exact HM47|]. split; [exact HMal|].
  intros a Ha. rewrite MB1 by (unfold IC_STK; lia). exact (HMZ a Ha). }
assert (HRO1 : YE01.arodata_okS tfibsegs B rlo rhi (aview tfibsegs (w_H W) mem1)).
{ intros a Hra' Hns Hne. pose proof (HRO a Hra' Hns Hne) as Hr0.
  rewrite <- (Z_to_bv64_of_mod a) in Hr0 |- *. rewrite AE2y.aview_mod in Hr0 |- *.
  assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  set (a' := a mod 2 ^ 64) in *.
  destruct (Z_lt_le_dec a' (spZ regs - IC_STK)) as [L|L]; [rewrite AV1 by lia; exact Hr0|].
  destruct (Z_lt_le_dec a' (spZ regs)) as [L2|L2]; [|rewrite AV1 by lia; exact Hr0].
  exfalso. unfold IC_STK in L. pose proof (Hpres a' ltac:(lia)) as Hp.
  apply (AE2y.aview_some_of_apresent _ _ _ Hp). rewrite Hr0.
  rewrite AF0x.seg_rom_none_high; [reflexivity|]. change AF0x.TFIB_IMG_END with (symaddr ImgPages.Asan.top). lia. }
(* ---- musl fclose, by its contract ---- *)
eapply SRr_bind.
{ apply (afclose_source_spec_musl W ly S regs1 mem1 md1 [] f b M C p rest P1 R10 Hperm HSRC1 Hbuf HMI1 HRO1 Hev Hu1 Hu2). }
cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & Jm & AP & R10' & Hperm' & Hfr' & Hnone & Hgarr & Hfds & Hfs).
rewrite R1. change (mkCfg (mkst regs' (YG0d.w64 IC_RET) mem' (seg_rom tfibsegs)) md') with (cfg_at tfibsegs IC_RET regs' mem' md').
pose proof Jm as (_ & _ & _ & _ & _ & _ & _ & _ & F1m & _).
assert (E2' : spZ regs' = spZ regs + -96).
{ transitivity (spZ regs1); [unfold spZ; f_equal; exact (AP 2 ltac:(unfold acallee_saved; lia)) | exact Esp1]. }
assert (G19' : getr regs' 19 = YG0d.w64 0) by (etransitivity; [exact (AP 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
(* the five words the front saved at sp0 - 8 .. sp0 - 40 survive musl fclose: they lie above its window *)
assert (SV : forall j rz off, nth_error SAVEDC j = Some (rz, off) ->
  val_mem tfibsegs (rd W2 mem') (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. pose proof (RSV j rz off Hj) as Hv.
  assert (Hoff : -40 <= off <= -8) by (do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
  apply (AF0x.val_mem_ext (rd W mem1)); [|exact Hv]. intros k Hk.
  apply AE2y.mbyte_of_aview. apply F1m; rewrite ?Esp1; unfold PFCLOSE_MUSL_STK, PFCLOSE_STK; lia. }
(* ---- the tail: 0x46838 .. ret ---- *)
eapply SRr_bind.
{ apply (iclose_tail W2 regs' mem' md' (bv_unsigned (getr regs (Z_to_bv 5 1))) (bv_unsigned (getr regs (Z_to_bv 5 8)))
    (bv_unsigned (getr regs (Z_to_bv 5 9))) (bv_unsigned (getr regs (Z_to_bv 5 18))) (bv_unsigned (getr regs (Z_to_bv 5 19)))).
  - exact G19'.
  - rewrite E2'. lia.
  - rewrite E2'. unfold IC_FRAME. lia.
  - rewrite E2'. replace (spZ regs + -96) with (spZ regs + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - rewrite E2'. replace (spZ regs + -96 + 88) with (spZ regs + -8) by lia. exact (SV 0%nat 1 (-8) eq_refl).
  - rewrite E2'. replace (spZ regs + -96 + 80) with (spZ regs + -16) by lia. exact (SV 1%nat 8 (-16) eq_refl).
  - rewrite E2'. replace (spZ regs + -96 + 72) with (spZ regs + -24) by lia. exact (SV 2%nat 9 (-24) eq_refl).
  - rewrite E2'. replace (spZ regs + -96 + 64) with (spZ regs + -32) by lia. exact (SV 3%nat 18 (-32) eq_refl).
  - rewrite E2'. replace (spZ regs + -96 + 56) with (spZ regs + -40) by lia. exact (SV 4%nat 19 (-40) eq_refl).
  - apply u64_range.
  - apply u64_range.
  - apply u64_range.
  - apply u64_range.
  - apply u64_range.
  - exact (wfi_ret_ok_even _ Hra). }
cbv beta. intros W3 c3 _ (-> & regs2 & md2 & -> & MF2 & T1 & T2 & T8 & T9 & T18 & T19 & TK).
apply SRr_ret.
(* ---- the post ---- *)
assert (J : ajournal (SK:=SK) tfibsegs B PFCLOSE_STK (spZ regs) (asource_fp f) ly S W mem md ([] ++ []) ly' S' W2 mem' md' (0 + 2)).
{ apply (YC85G.ajournal_sub_tok (SK:=SK) tfibsegs B LAWS ACeg.tfib_segs_low PFCLOSE_STK (spZ regs) (asource_fp f)
    ly S W mem md [] ly S W mem1 md1 0 PFCLOSE_MUSL_STK (spZ regs1) (asource_fp f) [] ly' S' W2 mem' md' 2 J0 Jm).
  - rewrite Esp1. unfold PFCLOSE_MUSL_STK, PFCLOSE_STK. lia.
  - rewrite Esp1. lia.
  - intros a Ha. left. exact Ha. }
assert (RKT : forall r, In r KEPTC -> In r KEPTT -> acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r H1 H2 H3. etransitivity; [exact (TK r H2)|]. etransitivity; [exact (AP r H3)|]. exact (RK r H1). }
exists ly', S', regs2, mem', md2.
split.
{ f_equal. f_equal. unfold YG0d.w64. apply Z_to_bv_bv_unsigned. }
split.
{ exact (ajournal_exec (SK:=SK) tfibsegs B LAWS ACeg.tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem' md2 (fun _ => False) J
    (fun _ _ => eq_refl) (mem_grows_refl _) (fun _ _ => eq_refl) MF2 (fun a Ha => False_ind _ Ha)). }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - etransitivity; [exact T2|]. rewrite E2'. unfold IC_FRAME, YG0d.w64.
    replace (spZ regs + -96 + 96) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - apply RKT; [unfold KEPTC; cbn; lia | unfold KEPTT; cbn; lia | unfold acallee_saved; lia].
  - apply RKT; [unfold KEPTC; cbn; lia | unfold KEPTT; cbn; lia | unfold acallee_saved; lia].
  - etransitivity; [exact T8|]. unfold YG0d.w64. apply Z_to_bv_bv_unsigned.
  - etransitivity; [exact T9|]. unfold YG0d.w64. apply Z_to_bv_bv_unsigned.
  - assert (Hc : r = 18 \/ r = 19 \/ 20 <= r <= 27) by lia.
    destruct Hc as [-> | [-> | Hc]].
    + etransitivity; [exact T18|]. unfold YG0d.w64. apply Z_to_bv_bv_unsigned.
    + etransitivity; [exact T19|]. unfold YG0d.w64. apply Z_to_bv_bv_unsigned.
    + apply RKT; [unfold KEPTC; cbn; lia | unfold KEPTT; cbn; lia | unfold acallee_saved; lia]. }
split.
{ etransitivity; [exact (TK 10 ltac:(unfold KEPTT; cbn; lia))|]. exact R10'. }
split; [exact Hperm'|].
split; [exact Hfr'|].
split; [exact Hnone|].
split; [exact Hgarr|].
rewrite (same_but_materialized_wvb _ _ MF2), (proj1 (wfi_wvb_io _ _ _)), (proj2 (wfi_wvb_io _ _ _)), Hfds, Hfs.
rewrite (same_but_materialized_wvb _ _ MF1), (proj1 (wfi_wvb_io _ _ _)), (proj2 (wfi_wvb_io _ _ _)).
split; reflexivity.
Qed.

End I.

(* The closed statement: the two Section hypotheses are now its arguments, TB and afclose_source_spec_musl. *)
Check (@afclose_source_spec_icpt :
  forall {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head) (B : asyms) (rlo rhi : Z),
  PcapSyms B ->
  afclose_source_spec_stk SK tfibsegs B pcap_KS PFCLOSE_MUSL_STK PFCLOSE_MUSL WFI_FREE1 WFI_JOIN rlo rhi ->
  afclose_source_spec SK tfibsegs B pcap_KS IC_ENTRY WFI_FREE1 WFI_JOIN rlo rhi).

(* The closure of every theorem in this file: no axiom outside toolchain/allowed-axioms.txt. *)
Print Assumptions wfi_ret_ok_even.
Print Assumptions wfi_in_img_of_b.
Print Assumptions wfi_img_top_page.
Print Assumptions wfi_seg_ro.
Print Assumptions wfi_ro_chunks_unowned.
Print Assumptions wfi_ic_cells_chk.
Print Assumptions wfi_wvb_io.
Print Assumptions wfi_env_low.
Print Assumptions wfi_vm_fr.
Print Assumptions wfi_head_env_addr.
Print Assumptions wfi_env_tr.
Print Assumptions wfi_asource_at_tr.
Print Assumptions wfi_cells_hold_of_chk.
Print Assumptions wfi_ro_img_of_arodata.
Print Assumptions afclose_source_spec_icpt.
