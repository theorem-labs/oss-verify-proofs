(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSbz_str.v, with its module paths and module names changed; 125 of its 195 lines of code are new or changed and 89 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxa_bzcj.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* The generic bridge between the Bz tree's walks (lib/A/Bz) and GXA's CJ call contracts (lib/CJ/RL/GXA), at the
   ASan instance A_img (RT_IImgA.v) on the pinned fuzz_manifest.asan.  Nothing here is about one interceptor: each
   GXA call-contract proof (strnlen in RT_gxa_strnlen.v; memcpy, memset) imports it.
   - the vocabulary: the Bz tree (lib/A/Bz/Lib) and the CJ tree (lib/CJ/Lib) are two copies of the same machine
     library.  Every definition used here is the same term in both, so it converts by `exact`, except two:
     `msteps` (an Inductive in each tree; bz_cj_msteps, bz_cj_evt) and `mem_inv` (CJ: every byte is outside read-only
     segments and inside a segment or below TASK_SIZE; Bz: every byte and every segment byte is below UTOP).
     TASK_SIZE = UTOP = 2^47, and every segment of fuzz_manifest.asan ends below 2^47 (asegs_below).
   - the shadow: chk_ok_of_pf_rng gives the interceptors' range check `chk_ok` (Bz/A/I_qck.v) from GXA's own ASan
     vocabulary (AsanFacts.v pf_rng / shadow_rw), the quick-check words through ro_C8_of_vis.
   No address numerals. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan; the image-generic lemmas of proofs/plugin-hostd/fuzz_reply/lib/A/RT_gxa_calls.v (ms_cj_bz .. mem_inv_bz_cj, shad_eq .. chk_ok_of_pf_rng), module path fuzz_reply -> fuzz_manifest, the Local lemmas made global, FRbz_str's Z_to_le_bytes_roundtrip / word_of_mem / ro_C8_of_vis copied in from omx-clap-core/fuzz_manifest's lib/A/FMbz_str.v:99-152 (proofs unchanged) so the closure has no Reusable file, split out of RT_gxa_strnlen.v so the memcpy and memset contracts can import them; proofs unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib Require Import Mem Bytes Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Common.PropExec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.PropExec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.RT_IImgA.
Import ListNotations.
Open Scope Z_scope.

Module BzP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Common.PropExec.
Module BzS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib.MState.
Module BzE := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib.Mem.
Module BzF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib.Frame.
Module CJP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.PropExec.
Module CJS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.MState.
Module CJE := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Exec.
Module CJM := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Frame.
Module CJR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RStep.
Module GXF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA.AsanFacts.
Module RTA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.RT_IImgA.

(* ---- the two trees' vocabularies ---- *)

Lemma ms_cj_bz : forall R F pc fc rv m ro, CJS.MS R F pc fc rv m ro = BzS.MS R F pc fc rv m ro.
Proof. reflexivity. Qed.

Lemma mkR_cj_bz : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  CJF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
  = BzF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. reflexivity. Qed.

Lemma seg_rom_cj_bz : CJP.seg_rom (@CJR.img_segs RTA.A_img) = BzP.seg_rom asegs.
Proof. reflexivity. Qed.

Lemma bz_cj_msteps : forall s s', BzE.msteps asegs s s' -> CJE.msteps (@CJR.img_segs RTA.A_img) s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply CJE.msteps_refl.
  - eapply CJE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma bz_cj_evt : forall Q ms, BzE.evt asegs Q ms -> CJE.evt (@CJR.img_segs RTA.A_img) Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (bz_cj_msteps ms ms' H) | exact HQ]. Qed.

Lemma find_segment_rng : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. lia.
  - destruct (IH a n seg H) as (Hi & H1 & H2). split; [right; exact Hi|]. lia.
Qed.

(* every segment of fuzz_manifest.asan ends below 2^47 *)
Lemma asegs_below : forall a : word, BzM.seg_addr asegs a = true -> bv_unsigned a < BzM.UTOP.
Proof.
  intros a H. unfold BzM.seg_addr in H.
  destruct (find_segment asegs (bv_unsigned a) 1) as [sg|] eqn:E; [|discriminate].
  destruct (find_segment_rng _ _ _ _ E) as (I & _ & R).
  assert (B : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 2 ^ 47) asegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B sg I). apply Z.leb_le in B. unfold BzM.UTOP. lia.
Qed.

Lemma mem_inv_cj_bz : forall m, CJM.mem_inv (@CJR.img_segs RTA.A_img) m -> BzM.mem_inv asegs m.
Proof.
  intros m H. apply BzM.mem_inv_intro; [exact asegs_below|].
  intros a b E. destruct (H a b E) as [[R S]|[R T]].
  - split; [exact R|]. apply asegs_below. unfold BzM.seg_addr.
    change (find_segment asegs (bv_unsigned a) 1 <> None) in S.
    destruct (find_segment asegs (bv_unsigned a) 1); [reflexivity | congruence].
  - split; [exact R|]. unfold BzM.UTOP. unfold TASK_SIZE in T. lia.
Qed.

Lemma mem_inv_bz_cj : forall m, BzM.mem_inv asegs m -> CJM.mem_inv (@CJR.img_segs RTA.A_img) m.
Proof.
  intros m H a b E. right. split.
  - exact (BzM.mem_inv_ro asegs m a b H E).
  - pose proof (BzM.mem_inv_ov_below asegs m a b H E) as B. unfold BzM.UTOP in B. unfold TASK_SIZE. lia.
Qed.

(* ---- GXA's ASan vocabulary in the walks' words: the interceptors' range check from pf_rng ---- *)

(* the quick check's aligned shadow words: eight readable bytes are an 8-byte cell (lib/A/FMbz_str.v:99-152) *)

(* the inverse of Mem.v:497: a byte list is what its own little-endian value spells *)
Lemma Z_to_le_bytes_roundtrip : forall (bs : list byte),
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  assert (Hrest : 0 <= bytes_le_to_Z bs)
    by (rewrite bytes_le_to_Z_le_val; pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)); lia).
  rewrite lor_shiftl8_add by lia.
  assert (Hhead : Z_to_bv 8 (bv_unsigned b + 256 * bytes_le_to_Z bs) = b).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite (Z.mul_comm 256 (bytes_le_to_Z bs)), Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (Htail : Z.shiftr (bv_unsigned b + 256 * bytes_le_to_Z bs) 8 = bytes_le_to_Z bs).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite (Z.mul_comm 256 (bytes_le_to_Z bs)), Z.div_add by lia.
    rewrite (Z.div_small (bv_unsigned b) 256) by lia. lia. }
  rewrite Hhead, Htail, IH. reflexivity.
Qed.

(* eight readable bytes are an 8-byte cell: the word they spell *)
Definition word_of_mem (m : word -> option byte) (a : Z) : word :=
  le_bytes_to_word (map (fun j => match mrd asegs m (wa (a + Z.of_nat j)) with
                                  | Some b => b | None => Z_to_bv 8 0 end) (seq 0 8)).

Lemma ro_C8_of_vis : forall (m : word -> option byte) a,
  0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall j, 0 <= j < 8 -> exists b, bytes_at asegs m (a + j) [b]) ->
  ro_cells asegs m a [C8 (word_of_mem m a)].
Proof.
  intros m a Ha Ha8 HB.
  set (bs := map (fun j => match mrd asegs m (wa (a + Z.of_nat j)) with
                           | Some b => b | None => Z_to_bv 8 0 end) (seq 0 8)).
  assert (Hlen : length bs = 8%nat) by (subst bs; rewrite length_map, length_seq; reflexivity).
  assert (Hbs : bytes_at asegs m a bs).
  { split; [lia|]. split; [rewrite Hlen; cbn; lia|].
    intros i Hi. rewrite Hlen in Hi.
    destruct (HB (Z.of_nat i) ltac:(lia)) as (b & _ & _ & Hb).
    specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb. rewrite Z.add_0_r in Hb.
    subst bs. rewrite nth_error_map, nth_error_seq.
    replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    cbn [option_map Nat.add]. rewrite Hb. reflexivity. }
  assert (Hval : bv_unsigned (le_bytes_to_word bs) = bytes_le_to_Z bs).
  { unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small.
    rewrite bytes_le_to_Z_le_val.
    pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr.
    rewrite length_map, Hlen in Hr. change (256 ^ Z.of_nat 8) with (2 ^ 64) in Hr. lia. }
  assert (Heq : le8 (le_bytes_to_word bs) = bs).
  { unfold le8, word_to_le_bytes. rewrite Hval, <- Hlen. apply Z_to_le_bytes_roundtrip. }
  split; [cbn; lia|].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r.
  unfold word_of_mem. fold bs. rewrite Heq. exact Hbs.
Qed.

Lemma shad_eq : forall x, shad x = GXF.shadow_addr x.
Proof. intros x. unfold shad, SHB, GXF.shadow_addr, GXF.ASAN_K. lia. Qed.

(* a byte GXA's reader sees is a byte the walks can read *)
Lemma bytes_at1_of_mrd : forall (m : word -> option byte) a b,
  0 <= a < 2 ^ 64 -> CJM.mrd (@CJR.img_segs RTA.A_img) m (CJM.wa a) = Some b -> bytes_at asegs m a [b].
Proof.
  intros m a b Ha H. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
  cbn [nth_error]. rewrite Z.add_0_r. exact H.
Qed.

(* GXA reads a shadow byte signed (AsanFacts.v:20), the walks unsigned (Shadow.v:16); on 0..7 they agree *)
Lemma sh_ok_of_shadow_ok : forall (b : byte) a, GXF.shadow_ok a (bv_signed b) -> sh_ok b a.
Proof.
  intros b a H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold GXF.shadow_ok, bv_signed, bv_swrap, bv_wrap in H. unfold sh_ok.
  change (bv_half_modulus 8) with 128 in H. change (bv_modulus 8) with 256 in H, R.
  Z.div_mod_to_equations. lia.
Qed.

(* the quick check's aligned shadow word of an application byte lies in ASan's shadow *)
Lemma al8_shad_in_shadow : forall x j, GXF.app_mem x -> 0 <= j < 8 -> GXF.in_shadow (al8 (shad x) + j).
Proof.
  intros x j H Hj.
  unfold GXF.app_mem, GXF.in_shadow, GXF.LOWMEM_END, GXF.LOWSHADOW_END, GXF.HIGHSHADOW_BEG, GXF.HIGHMEM_BEG,
    GXF.APPMEM_END, al8, shad, SHB in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma qc_word_of_shadow_rw : forall (m : word -> option byte) x,
  @GXF.shadow_rw RTA.A_img m -> GXF.app_mem x ->
  ro_cells asegs m (al8 (shad x)) [C8 (word_of_mem m (al8 (shad x)))].
Proof.
  intros m x SRW Hx.
  assert (B : 0 <= al8 (shad x) /\ al8 (shad x) + 8 <= 2 ^ 64).
  { unfold GXF.app_mem, GXF.LOWMEM_END, GXF.HIGHMEM_BEG, GXF.APPMEM_END, al8, shad, SHB in *.
    Z.div_mod_to_equations. lia. }
  apply ro_C8_of_vis; [lia | lia |].
  intros j Hj. pose proof (al8_shad_in_shadow x j Hx Hj) as HS.
  destruct (SRW _ HS) as (_ & b & Hb). exists b.
  apply bytes_at1_of_mrd; [| exact Hb].
  unfold GXF.in_shadow, GXF.LOWMEM_END, GXF.LOWSHADOW_END, GXF.HIGHSHADOW_BEG, GXF.HIGHMEM_BEG in HS. lia.
Qed.

(* the interceptor's range check on any prefix of a range GXA calls addressable, given a readable shadow *)
Lemma chk_ok_of_pf_rng : forall (m : word -> option byte) p n k,
  @GXF.pf_rng RTA.A_img m p n -> @GXF.shadow_rw RTA.A_img m -> k <= n -> chk_ok m p k.
Proof.
  intros m p n k (HN & (Hp & Hn & Hpn & AD) & _ & SEVEN) SRW Hk.
  unfold GXF.APPMEM_END in Hpn.
  split; [| split].
  - intros i Hi. destruct (AD i ltac:(lia)) as (APP & b & Hb & Hok).
    exists b. split.
    + rewrite shad_eq. apply bytes_at1_of_mrd; [| exact Hb].
      unfold GXF.shadow_addr, GXF.ASAN_K. Z.div_mod_to_equations. lia.
    + apply sh_ok_of_shadow_ok. exact Hok.
  - intros Hk1.
    destruct (AD 0 ltac:(lia)) as (A0 & _). rewrite Z.add_0_r in A0.
    destruct (AD (k - 1) ltac:(lia)) as (A1 & _). replace (p + (k - 1)) with (p + k - 1) in A1 by lia.
    exists (word_of_mem m (al8 (shad p))), (word_of_mem m (al8 (shad (p + k - 1)))).
    split; apply qc_word_of_shadow_rw; assumption.
  - intros Hk0. split; [| lia].
    destruct (AD 0 ltac:(lia)) as (A0 & _). rewrite Z.add_0_r in A0.
    pose proof (SEVEN (k - 1) ltac:(lia)) as A7.
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd.
    unfold GXF.app_mem, GXF.LOWMEM_END, GXF.HIGHMEM_BEG, GXF.APPMEM_END in A0, A7. lia.
Qed.
