(* SPDX-License-Identifier: MIT *)
(** The library contract of ADPCM_IMA_WAV's LLVMFuzzerTestOneInput, from the
    symbolic tree of AHarness: on entry, the FFmpeg globals it reads and
    writes hold whatever they hold (atoms 40, 41, 42); on return a0 = 0, the
    callee-saved registers are restored, and memory differs only in its frame
    and in [ms_hw]. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import
  YK11 YK0i YK0o YK15 YP0m YP09 YP0l YP02 YP03 YP06 YP0g YM06 YI04
  YM05 YO0i YO0f YO0d YO05 YO09 YN03 YH00 YH02 YH03 YI14 YI16 YI5b YI5c
  YL01 YL0g YL0i YL0s YL08 YK0w YN01.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require YN2e.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib Require Import
  ZImage ZTraceSpec ZComplete ZAllocator AHarness.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import YAddr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Definition in_hw (a : Z) : Prop := exists q, In q (ms_hw src0_msyms) /\ fst q <= a < snd q.
Lemma in_hw_iff : forall a, in_hw a <->
  ((AX_reset_cpu_flags_default_cpu_flags) <= a < (AX_cpu_count) \/ (AX_av_log_level) <= a < (AX_av_log_level_end) \/ (AX_c) <= a < (AX_av_cpu_count_printed) \/ (AX_codec_list) <= a < (AX_codec_list_8)).
Proof.
  intros a. split.
  - intros (q & Hq & Ha). cbn in Hq. destruct Hq as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia.
  - intros [H|[H|[H|H]]];
      [exists ((AX_reset_cpu_flags_default_cpu_flags), (AX_cpu_count)) | exists ((AX_av_log_level), (AX_av_log_level_end)) | exists ((AX_c), (AX_av_cpu_count_printed)) | exists ((AX_codec_list), (AX_codec_list_8))];
      (split; [cbn; tauto | cbn [fst snd]; lia]).
Qed.

Section Pure.
Context {fx : FPState}.

Lemma hw_rw : forall mem x, in_hw x -> writable_at zsegs mem x /\ exists b, mbyte zsegs mem x = Some b.
Proof.
  intros mem x Hx. apply in_hw_iff in Hx.
  destruct Hx as [H|[H|[H|H]]].
  - exact (rw_check_sound src0_msyms 8 (AX_reset_cpu_flags_default_cpu_flags) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) mem x ltac:(lia)).
  - exact (rw_check_sound src0_msyms 4 (AX_av_log_level) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) mem x ltac:(lia)).
  - exact (rw_check_sound src0_msyms 8 (AX_c) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) mem x ltac:(lia)).
  - exact (rw_check_sound src0_msyms 8 (AX_codec_list) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) mem x ltac:(lia)).
Qed.

Lemma ah_le_byte4 (v0 v1 v2 v3 : Z) k :
  0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> (k < 4)%nat ->
  le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 k = nth k [v0; v1; v2; v3] 0.
Proof.
  intros H0 H1 H2 H3 Hk. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
  rewrite (Z.mod_small _ 4294967296) by lia. rewrite Z.shiftr_div_pow2 by lia.
  destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth Z.of_nat Z.mul Pos.of_succ_nat Pos.mul Pos.succ].
  - change (2 ^ 0) with 1. rewrite Z.div_1_r.
    replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with (v0 + (v1 + 256 * v2 + 65536 * v3) * 256) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - change (2 ^ 8) with 256.
    replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with (v0 + (v1 + (v2 + 256 * v3) * 256) * 256) by lia.
    rewrite Z.div_add, Z.div_small, Z.add_0_l, Z_mod_plus_full by lia. apply Z.mod_small. lia.
  - change (2 ^ 16) with 65536.
    replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with ((v0 + 256 * v1) + (v2 + v3 * 256) * 65536) by lia.
    rewrite Z.div_add, Z.div_small, Z.add_0_l, Z_mod_plus_full by lia. apply Z.mod_small. lia.
  - change (2 ^ 24) with 16777216.
    replace (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) with ((v0 + 256 * v1 + 65536 * v2) + v3 * 16777216) by lia.
    rewrite Z.div_add, Z.div_small, Z.add_0_l by lia. apply Z.mod_small. lia.
Qed.
Lemma bytes4_any : forall m a,
  (forall k, (k < 4)%nat -> exists b, mbyte zsegs m (a + Z.of_nat k) = Some b) ->
  exists v, 0 <= v < 2 ^ 32 /\ forall k, (k < 4)%nat -> mbyte zsegs m (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 4 k)).
Proof.
  intros m a B.
  destruct (B 0%nat ltac:(lia)) as [b0 H0]. destruct (B 1%nat ltac:(lia)) as [b1 H1].
  destruct (B 2%nat ltac:(lia)) as [b2 H2]. destruct (B 3%nat ltac:(lia)) as [b3 H3].
  pose proof (u8_range b0). pose proof (u8_range b1). pose proof (u8_range b2). pose proof (u8_range b3).
  exists (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
  split; [lia|]. intros k Hk. rewrite ah_le_byte4 by assumption.
  destruct k as [|[|[|[|k]]]]; [rewrite H0 | rewrite H1 | rewrite H2 | rewrite H3 | lia]; cbn [nth];
    rewrite Z_to_bv_bv_unsigned; reflexivity.
Qed.
Lemma bytes8_any : forall m a,
  (forall k, (k < 8)%nat -> exists b, mbyte zsegs m (a + Z.of_nat k) = Some b) ->
  exists v, 0 <= v < 2 ^ 64 /\ forall k, (k < 8)%nat -> mbyte zsegs m (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 8 k)).
Proof.
  intros m a B.
  destruct (B 0%nat ltac:(lia)) as [b0 H0]. destruct (B 1%nat ltac:(lia)) as [b1 H1].
  destruct (B 2%nat ltac:(lia)) as [b2 H2]. destruct (B 3%nat ltac:(lia)) as [b3 H3].
  destruct (B 4%nat ltac:(lia)) as [b4 H4]. destruct (B 5%nat ltac:(lia)) as [b5 H5].
  destruct (B 6%nat ltac:(lia)) as [b6 H6]. destruct (B 7%nat ltac:(lia)) as [b7 H7].
  set (bs := [b0; b1; b2; b3; b4; b5; b6; b7]).
  exists (bytes_le_to_Z bs). split; [apply bytes_le_to_Z_range; reflexivity|].
  intros k Hk. rewrite le_byte_bytes_le_to_Z by (reflexivity || exact Hk).
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]];
    [rewrite H0 | rewrite H1 | rewrite H2 | rewrite H3 | rewrite H4 | rewrite H5 | rewrite H6 | rewrite H7 | lia];
    cbn [nth bs]; rewrite Z_to_bv_bv_unsigned; reflexivity.
Qed.

Definition ah_env (regs : bvmap 5 word) (v40 v41 v42 : Z) : env :=
  mkEnv (fun n => if Nat.ltb n 32 then getr regs (Z_to_bv 5 (Z.of_nat n))
                  else if Nat.eqb n 40 then Z_to_bv 64 v40
                  else if Nat.eqb n 41 then Z_to_bv 64 v41 else Z_to_bv 64 v42) (fun _ => []).
Lemma ah_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma ah_regs_ok : forall regs v40 v41 v42,
  getr regs (Z_to_bv 5 1) = Z_to_bv 64 RA_LIB -> regs_ok (ah_env regs v40 v41 v42) ah_regs regs.
Proof.
  intros regs v40 v41 v42 Hra r.
  pose proof (u5_range r) as Hr.
  remember (Z.to_nat (bv_unsigned r)) as n eqn:Hidx.
  assert (Hlt : (n < 32)%nat) by lia.
  assert (R : r = Z_to_bv 5 (Z.of_nat n)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 5 (Z.of_nat n)) with (Z.of_nat n mod 32).
    rewrite Z.mod_small by lia. lia. }
  subst r.
  do 32 (destruct n as [|n]; [
    lazymatch goal with |- getr ?rr ?r = _ =>
      let v := eval vm_compute in (sr_get ah_regs r) in
      change (getr rr r = sv_denot (ah_env rr v40 v41 v42) v)
    end;
    first [exact Hra | reflexivity | rewrite ah_denot_off0; reflexivity] |]).
  lia.
Qed.
Lemma ah_region_ok_intro : forall E m r,
  0 <= base_val E (r_base r) + r_lo r -> base_val E (r_base r) + r_hi r <= 2 ^ 64 ->
  (forall o, r_wlo r <= o < r_whi r -> writable_at zsegs m (base_val E (r_base r) + o)) ->
  Forall (chunk_ok zsegs E m (base_val E (r_base r))) (r_chunks r) ->
  region_ok zsegs E m r.
Proof. intros E m r H1 H2 H3 H4. unfold region_ok. auto. Qed.
Lemma ah_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.
Lemma ah_chunk_ok_cval : forall E m off (w : nat) v (val : Z),
  sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
  (forall k, (k < w)%nat -> mbyte zsegs m (off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte val w k))) ->
  chunk_ok zsegs E m 0 (mkChunk off (CVal (N.of_nat w) v)).
Proof.
  intros E m off w v val Hv Hval H i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
  rewrite nat_N_Z in Hi. rewrite !Z.add_0_l.
  exists (byte_of_word (sv_denot E v) i). split; [reflexivity|].
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite H by lia.
  f_equal. rewrite YN2e.le_byte_bv by lia. unfold byte_of_word. rewrite Hv, ah_u64 by lia.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma ah_chunk_ok_img : forall E m off (len : Z),
  (forall i, 0 <= i < len -> mbyte zsegs m (off + i) = seg_rom zsegs (Z_to_bv 64 (off + i))) ->
  (forall i, 0 <= i < len -> seg_rom zsegs (Z_to_bv 64 (off + i)) <> None) ->
  chunk_ok zsegs E m 0 (mkChunk off (CImg len)).
Proof.
  intros E m off len Hm Hs i Hi. cbn [c_off c_val c_len cv_len cbyte img_byte] in Hi |- *.
  rewrite !Z.add_0_l. destruct (seg_rom zsegs (Z_to_bv 64 (off + i))) as [b|] eqn:Eb.
  - exists b. split; [unfold img_byte; exact Eb|]. rewrite Hm by exact Hi. exact Eb.
  - exfalso. exact (Hs i Hi Eb).
Qed.

Section Entry.
Context {rc : RunCeil}.
Variables (regs : bvmap 5 word) (mem : word -> option byte) (v40 v41 v42 : Z).
Let E := ah_env regs v40 v41 v42.
Let sp := bv_unsigned (getr regs (Z_to_bv 5 2)).
Hypothesis Hra : getr regs (Z_to_bv 5 1) = Z_to_bv 64 RA_LIB.
Hypothesis Hsp : alloc_ceiling + LIB_STACK <= sp.
Hypothesis Hsp63 : sp < 2 ^ 63.
Hypothesis Hal : sp mod 16 = 0.
Hypothesis Hstk : forall a, sp - LIB_STACK <= a < sp -> writable_at zsegs mem a.
Hypothesis Hro : rodata_ok src0_msyms mem.
Hypothesis R40 : 0 <= v40 < 2 ^ 32.
Hypothesis R41 : 0 <= v41 < 2 ^ 32.
Hypothesis R42 : 0 <= v42 < 2 ^ 64.
Hypothesis B40 : forall k, (k < 4)%nat -> mbyte zsegs mem ((AX_reset_cpu_flags_default_cpu_flags) + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v40 4 k)).
Hypothesis B41 : forall k, (k < 4)%nat -> mbyte zsegs mem ((AX_cpu_flags) + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v41 4 k)).
Hypothesis B42 : forall k, (k < 8)%nat -> mbyte zsegs mem ((AX_c) + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v42 8 k)).
Lemma ah_base_sp : base_val E (Some 2%nat) = sp.
Proof. reflexivity. Qed.
Lemma ah_hr_img : forall lo len a, In (lo, lo + len) (ms_hr src0_msyms) -> lo <= a < lo + len ->
  mbyte zsegs mem a = seg_rom zsegs (Z_to_bv 64 a).
Proof. intros lo len a Hin Ha. apply Hro. right. exists (lo, lo + len). split; [exact Hin | cbn [fst snd]; lia]. Qed.
Lemma ah_entry_ok : st_ok zsegs E ah_entry (mkst regs (Z_to_bv 64 LIBPC) mem (seg_rom zsegs)).
Proof.
  pose proof alloc_ceiling_val as HC. unfold LIB_STACK in *.
  unfold st_ok. cbn [mkst ah_entry ss_pc ss_resv ss_regs ss_mem ss_facts].
  repeat (split; [reflexivity|]).
  split; [apply ah_regs_ok; exact Hra|].
  split.
  - split; [vm_compute; reflexivity|]. split.
    + unfold ah_mem. repeat apply Forall_cons; try apply Forall_nil.
      * apply ah_region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks ah_stack]; rewrite ?ah_base_sp; unfold AH_FRAME; try lia.
        -- intros o Ho. apply Hstk. lia.
        -- apply Forall_nil.
      * apply ah_region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks ah_flags base_val]; try lia.
        -- intros o Ho. apply (hw_rw mem). apply in_hw_iff. lia.
        -- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
           ++ apply (ah_chunk_ok_cval E mem _ 4 _ v40); [rewrite ah_denot_off0; reflexivity | lia | exact B40].
           ++ apply (ah_chunk_ok_cval E mem _ 4 _ v41); [rewrite ah_denot_off0; reflexivity | lia | exact B41].
      * apply ah_region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks ah_level base_val]; try lia.
        -- intros o Ho. apply (hw_rw mem). apply in_hw_iff. lia.
        -- apply Forall_nil.
      * apply ah_region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks ah_c base_val]; try lia.
        -- intros o Ho. apply (hw_rw mem). apply in_hw_iff. lia.
        -- apply Forall_cons; [|apply Forall_nil].
           apply (ah_chunk_ok_cval E mem _ 8 _ v42); [rewrite ah_denot_off0; reflexivity | lia | exact B42].
      * apply ah_region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks ah_list base_val]; try lia.
        -- intros o Ho. apply (hw_rw mem). apply in_hw_iff. lia.
        -- apply Forall_nil.
      * apply ah_region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks ah_type base_val]; try lia.
        apply Forall_cons; [|apply Forall_nil]. apply ah_chunk_ok_img.
        -- intros i Hi. apply (ah_hr_img (AX_ff_adpcm_ima_wav_encoder_10) 4); [cbn; tauto | cbn in Hi; lia].
        -- intros i Hi. cbn in Hi. assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
           destruct Hi' as [ -> | [ -> | [ -> | -> ]]]; vm_compute; discriminate.
      * apply ah_region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks ah_got base_val]; try lia.
        apply Forall_cons; [|apply Forall_nil]. apply ah_chunk_ok_img.
        -- intros i Hi. apply (ah_hr_img (AX_got_ff_adpcm_ima_wav_encoder) 16); [cbn; tauto | cbn in Hi; lia].
        -- intros i Hi. cbn in Hi.
           assert (Hk : exists k, i = Z.of_nat k /\ (k < 16)%nat) by (exists (Z.to_nat i); split; lia).
           destruct Hk as (k & -> & Hk).
           do 16 (destruct k as [|k]; [vm_compute; discriminate|]). lia.
    + unfold ah_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [r_base r_lo r_hi ah_stack ah_flags ah_level ah_c ah_list ah_type ah_got].
      rewrite !ah_base_sp. cbn [base_val]. unfold AH_FRAME. repeat split; lia.
  - split; [|split; exact I].
    cbn [ah_facts f_atoms atoms_ok]. split; [|exact I].
    assert (Hsp2 : bv_unsigned (ew E 2) = sp) by reflexivity.
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hsp2.
    change (2 ^ 4) with 16. repeat split; try lia.
Qed.
End Entry.
End Pure.

Section Post.
Context {fx : FPState} {rc : RunCeil}.
Let API := @adpcm_API rc.
Let MR := aa_MR API.
Lemma hw_img : forall a, in_hw a -> in_img src0_msyms a.
Proof. intros a Ha. apply in_hw_iff in Ha. apply src0_sink_in_img. lia. Qed.
Lemma hw_not_static : forall a, static_owned src0_msyms a -> ~ in_hw a.
Proof.
  intros a Hs Hh. apply in_hw_iff in Hh. unfold static_owned in Hs. cbn in Hs.
  unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32,
    src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_vmlock in Hs. lia.
Qed.
Lemma hw_not_ctx : forall a, ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE -> ~ in_hw a.
Proof. intros a Ha Hh. apply in_hw_iff in Hh. cbn in Ha. unfold src0_D_malloc_context, CTX_SIZE in Ha. lia. Qed.
Lemma hw_not_errno : forall a, errno_addr src0_msyms <= a < errno_addr src0_msyms + 4 -> ~ in_hw a.
Proof. intros a Ha Hh. apply in_hw_iff in Hh. unfold errno_addr in Ha. cbn in Ha. unfold src0_tp in Ha. lia. Qed.
Lemma hw_not_env : forall a, env_addr a -> ~ in_hw a.
Proof.
  intros a Ha Hh. apply in_hw_iff in Hh. unfold env_addr in Ha.
  cbv [sk_ofl_head sk_threaded sk_ofl_lock sk_path_addr sk_mode_addr sk_trailer_addr sk_rwa_addr sk_highs_addr sk_ones_addr src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc
    src0_D_str_tmp_out_gif src0_D_str_wb src0_D_str_3 src0_D_str_rwa src0_D_const_HIGHS_0x8080808080808080 src0_D_const_ONES_0x0101010101010100] in Ha. lia.
Qed.

Lemma ah_post : forall L A regs mem md p n pl b regs' mem',
  lib_pre_x src0_msyms API LIB_STACK EMPTY L A regs mem md RA_LIB p n pl b ->
  getr regs' (Z_to_bv 5 10) = Z_to_bv 64 0 ->
  regs_preserved regs regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - AH_FRAME <= a < spZ regs) -> ~ in_hw a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, spZ regs - AH_FRAME <= a < spZ regs -> writable_at zsegs mem' a) ->
  lib_post_x src0_msyms API LIB_STACK L A regs mem md p n b
    (LL 0 (m_fs md) []) L A regs' mem' md.
Proof.
  intros L A regs mem md p n pl b regs' mem' HP Hr Hregs HU HWnew.
  destruct HP as [HP [Hlen [HD [Hres [Hroom [HSink [Hfd [Hsorted Hsp47]]]]]]]].
  destruct HP as [HM [HW [HB [Hid [Hra [Hal [Hsp [HspHi [HWstack [Htp [HWerrno
    [Hptr [Hsize [Hlive Hro]]]]]]]]]]]]]].
  pose proof (@adpcm_allocator_extra rc) as AX. pose proof alloc_ceiling_val as HC.
  unfold LIB_STACK, AH_FRAME in *.
  assert (LOWU : forall a, 0 <= a < alloc_ceiling -> ~ in_hw a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hh. apply HU; [lia | lia | exact Hh]. }
  assert (WEQ : forall a, mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> (writable_at zsegs mem' a <-> writable_at zsegs mem a)).
  { intros a H. unfold writable_at, wview. rewrite H. reflexivity. }
  assert (OWN : forall a, owned src0_msyms L A a -> ~ in_hw a).
  { intros a [Ha|Ha] Hh.
    - exact (hw_not_ctx a (ax_img AX L A mem md a HM (hw_img a Hh) Ha) Hh).
    - exact (hw_not_static a Ha Hh). }
  assert (BLK : forall q k i, In (q, k) (user_blocks A) -> 0 <= i < k ->
    mem' (Z_to_bv 64 (ptr_addr L q + i)) = mem (Z_to_bv 64 (ptr_addr L q + i))).
  { intros q k i Hin Hi.
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k i HM Hin Hi) as (_ & Hlo & Hhi & _).
    apply LOWU; [lia|]. intros Hh. exact (ax_blocks_img AX L A mem md q k i HM Hin Hi (hw_img _ Hh)). }
  unfold lib_post_x. cbn [ll_ret ll_fs ll_out].
  split.
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as [Hh [Hl Hmat]].
    eapply (mr_frame _ _ (aa_laws API)); [exact HM| | | |reflexivity|exact Hh|exact Hl|exact Hmat].
    - intros a Ha. unfold mbyte. rewrite LOWU; [reflexivity | | exact (OWN a Ha)].
      exact (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ha).
    - intros a Ha [b0 Hb]. exists b0. rewrite LOWU; [exact Hb | | exact (OWN a Ha)].
      exact (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ha).
    - intros q k i Hin Hi.
      destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k i HM Hin Hi) as [[b0 Hb] _].
      exists b0. rewrite (BLK q k i Hin Hi). exact Hb. }
  split; [exact HW|]. split; [exact HB|]. split; [exact Hid|].
  split; [exact Hr|]. split; [exact Hregs|].
  split.
  { exists (m_vmmaps md), (m_fds md), (m_statpins md).
    split; [apply os_upd_self|]. intros k. reflexivity. }
  split.
  { intros q k Hin. exists q. auto. }
  split.
  { intros a Ha Hnot.
    assert (HR : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { apply HU; [lia | | intros Hh; apply in_hw_iff in Hh; lia].
      intros Hs. apply Hnot. unfold lib_scratch. left. lia. }
    split; [unfold mbyte; rewrite HR; reflexivity|]. apply iff_sym, WEQ, HR. }
  split.
  { intros a Himg Hstatic Hctx Herr Hhw.
    assert (Hnh : ~ in_hw a) by (intros (q & Hq & Haq); exact (Hhw q Hq Haq)).
    pose proof (so_img_hi _ src0_syms_ok a Himg) as Ha.
    assert (HR : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply LOWU; [lia | exact Hnh]).
    split; [unfold mbyte; rewrite HR; reflexivity|]. apply iff_sym, WEQ, HR. }
  split.
  { intros q k i Hin Hneq Hi. unfold mbyte. rewrite (BLK q k i Hin Hi). reflexivity. }
  split.
  { intros a [Ha|Ha].
    - destruct (Z_lt_le_dec a (spZ regs - 144)) as [Hlow|Hhigh].
      + apply (proj2 (WEQ a (HU a ltac:(lia) ltac:(lia) ltac:(intros Hh; apply in_hw_iff in Hh; lia)))).
        apply HWstack. exact Ha.
      + apply HWnew. lia.
    - assert (Hnh : ~ in_hw a) by exact (hw_not_errno a Ha).
      assert (Hlo : 0 <= a < alloc_ceiling) by (unfold errno_addr in Ha; cbn in Ha; unfold src0_tp in Ha; lia).
      apply (proj2 (WEQ a (LOWU a Hlo Hnh))). apply HWerrno. exact Ha. }
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hsorted|]. split.
  { eapply sink_none_frame; [|exact HSink]. intros a Ha.
    pose proof (src0_env_addr_range a Ha) as Har.
    unfold mbyte. rewrite LOWU; [reflexivity | lia | exact (hw_not_env a Ha)]. }
  split.
  { exact Hres. }
  intros i Hi. destruct Hlive as [[-> Hempty]|[Hpos [q [Hin Hq]]]].
  - lia.
  - rewrite <- Hq. unfold mbyte. rewrite (BLK q n i Hin Hi). reflexivity.
Qed.
End Post.

Lemma map_eq_at {A B} : forall (f g : A -> B) l x, map f l = map g l -> In x l -> f x = g x.
Proof.
  intros f g l x H Hin. induction l as [|y l IH]; [destruct Hin|].
  cbn in H. injection H as Hy Hl. destruct Hin as [<-|Hin]; [exact Hy | exact (IH Hl Hin)].
Qed.

Section Tree.
Context {fx : FPState}.
Lemma step_to : forall E ss ss' st ms m0 md Q,
  m_halted md = None -> m_vm_lazy md = [] ->
  st_ok zsegs E ss ms -> run_ ss = (ss', st) ->
  skeleton ah_mem = skeleton (ss_mem ss) -> frame_of E ah_mem m0 (ms_mem ms) ->
  (forall ms', match st with RS_ecall => st_ok_ecall zsegs E ss' ms' | _ => st_ok zsegs E ss' ms' end ->
     frame_of E ah_mem m0 (ms_mem ms') -> SR zsegs (mkCfg ms' md) Q) ->
  SR zsegs (mkCfg ms md) Q.
Proof.
  intros E ss ss' st ms m0 md Q Hh Hl HS Hrun Hsk HF K.
  eapply (SR_run_to_gen zsegs ztbl ztbl_ok AH_FUEL RA_LIB E ss ss' st ms md Q Hh Hl HS Hrun).
  intros ms' HS' HF'. apply K; [exact HS'|].
  exact (frame_of_trans E ah_mem (ss_mem ss) m0 (ms_mem ms) (ms_mem ms') Hsk HF HF').
Qed.
End Tree.

Theorem adpcm_harness_holds : adpcm_harness_contract.
Proof.
  intros rc. unfold lib_contract_x_all. intros fx. unfold lib_contract_x.
  intros L A regs mem md p n pl b K HP Hfrm HK.
  pose proof HP as HP'. destruct HP' as [HP0 _].
  destruct HP0 as [HM [HW [HB [Hid [Hra [Hal [Hsp [HspHi [HWstack [Htp [HWerrno
    [Hptr [Hsize [Hlive Hro]]]]]]]]]]]]]].
  pose proof alloc_ceiling_val as HC.
  destruct (bytes4_any mem (AX_reset_cpu_flags_default_cpu_flags) (fun k Hk => proj2 (hw_rw mem ((AX_reset_cpu_flags_default_cpu_flags) + Z.of_nat k) (proj2 (in_hw_iff ((AX_reset_cpu_flags_default_cpu_flags) + Z.of_nat k)) ltac:(left; lia)))))
    as (v40 & R40 & B40).
  destruct (bytes4_any mem (AX_cpu_flags) (fun k Hk => proj2 (hw_rw mem ((AX_cpu_flags) + Z.of_nat k) (proj2 (in_hw_iff ((AX_cpu_flags) + Z.of_nat k)) ltac:(left; lia)))))
    as (v41 & R41 & B41).
  destruct (bytes8_any mem (AX_c) (fun k Hk => proj2 (hw_rw mem ((AX_c) + Z.of_nat k) (proj2 (in_hw_iff ((AX_c) + Z.of_nat k)) ltac:(right; right; left; lia)))))
    as (v42 & R42 & B42).
  set (E := ah_env regs v40 v41 v42).
  assert (HS : st_ok zsegs E ah_entry (mkst regs (Z_to_bv 64 LIBPC) mem (seg_rom zsegs))).
  { apply ah_entry_ok; assumption. }
  destruct (mr_model _ _ (aa_laws adpcm_API) _ _ _ _ HM) as [Hh [Hl Hmat]].
  change (realizes zsegs (mkCfg (mkst regs (Z_to_bv 64 LIBPC) mem (seg_rom zsegs)) md) (K (LL 0 (m_fs md) []))).
  refine (SR_realizes zsegs _ _ _ _ (HK (LL 0 (m_fs md) []))).
  assert (Hsp2 : bv_unsigned (ew E 2) = spZ regs) by reflexivity.
  match goal with |- SR _ _ ?Q =>
    assert (LEAF : forall ss ms', leaf_facts ss -> st_ok zsegs E ss ms' -> frame_of E ah_mem mem (ms_mem ms') ->
      SR zsegs (mkCfg ms' md) Q) end.
  { intros ss ms' (Hpc & Hrv & Ha0 & Hsv & Hsk) HS' HF. apply SR_ret.
    pose proof (st_ok_mkst zsegs E ss ms' HS' Hrv) as Hshape. rewrite Hpc in Hshape.
    exists fx, L, A, (ms_regs ms'), (ms_mem ms'), md.
    split; [f_equal; exact Hshape|]. split; [exact Hfrm|].
    apply (ah_post L A regs mem md p n pl b); [exact HP | | | |].
    - rewrite (st_ok_reg zsegs _ _ _ (Z_to_bv 5 10) HS'), Ha0. reflexivity.
    - intros r Hr. assert (Hin : In r AH_SAVED) by (unfold callee_saved in Hr; cbn; lia).
      rewrite (st_ok_reg zsegs _ _ _ (Z_to_bv 5 r) HS').
      rewrite (map_eq_at (fun r => sr_get (ss_regs ss) (Z_to_bv 5 r)) (fun r => sr_get ah_regs (Z_to_bv 5 r)) AH_SAVED r Hsv Hin).
      symmetry. exact (ah_regs_ok regs v40 v41 v42 Hra (Z_to_bv 5 r)).
    - intros a Ha N1 N2. apply HF. rewrite ah_u64 by lia. intros (r & Hin & Hw).
      unfold ah_mem in Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
        cbn [r_base r_wlo r_whi ah_stack ah_flags ah_level ah_c ah_list ah_type ah_got] in Hw;
        rewrite ?Hsp2 in Hw; cbn [base_val] in Hw; rewrite ?Hsp2 in Hw; unfold AH_FRAME in *;
        first [lia | apply N2, in_hw_iff; lia].
    - intros a Ha. destruct (ss_mem ss) as [|r0 rs] eqn:Em; [discriminate Hsk|].
      unfold ah_mem, skeleton in Hsk. cbn [map] in Hsk. injection Hsk as Hb Hlo Hhi Hwlo Hwhi _.
      pose proof (mem_ok_region zsegs E (ms_mem ms') (ss_mem ss) r0 (st_ok_mem_ok zsegs _ _ _ HS')
        ltac:(rewrite Em; left; reflexivity)) as (_ & _ & HWr & _).
      specialize (HWr (a - spZ regs)). rewrite Hwlo, Hwhi, Hb in HWr. cbn [base_val] in HWr. rewrite Hsp2 in HWr.
      replace (spZ regs + (a - spZ regs)) with a in HWr by lia. apply HWr. unfold AH_FRAME in *. lia. }
  assert (IN1 : In ah_s1 [ah_s1; ah_s3; ah_s4]) by (cbn; tauto).
  assert (IN3 : In ah_s3 [ah_s1; ah_s3; ah_s4]) by (cbn; tauto).
  assert (IN4 : In ah_s4 [ah_s1; ah_s3; ah_s4]) by (cbn; tauto).
  assert (CS : In C_c_set [C_c_set; C_c_null]) by (cbn; tauto).
  assert (CN : In C_c_null [C_c_set; C_c_null]) by (cbn; tauto).
  apply (step_to E ah_entry ah_s0 _ _ mem md _ Hh Hl HS run_s0 eq_refl (frame_of_refl _ _ _)).
  intros ms1 HS1 HF1. change (st_ok zsegs E ah_s0 ms1) in HS1.
  apply (SR_branch_J zsegs E ah_s0 ms1 md _ BC_GE (SExt true 32 (SOff 40 0)) (SLit 0) HS1); intros _ HS1'.
  - apply (step_to E (add_cond ah_s0 C_def_ge) ah_s1 _ _ mem md _ Hh Hl HS1' run_s1 ltac:(vm_compute; reflexivity) HF1).
    intros ms2 HS2 HF2. change (st_ok zsegs E ah_s1 ms2) in HS2.
    apply (SR_branch_J zsegs E ah_s1 ms2 md _ BC_NE (SOff 42 0) (SLit 0) HS2); intros _ HS2'.
    + apply (step_to E (add_cond ah_s1 C_c_set) _ _ _ mem md _ Hh Hl HS2' (run_leaf _ _ IN1 CS) ltac:(vm_compute; reflexivity) HF2).
      intros ms3 HS3 HF3. exact (LEAF _ ms3 (leaves_ok _ _ IN1 CS) HS3 HF3).
    + apply (step_to E (add_cond ah_s1 C_c_null) _ _ _ mem md _ Hh Hl HS2' (run_leaf _ _ IN1 CN) ltac:(vm_compute; reflexivity) HF2).
      intros ms3 HS3 HF3. exact (LEAF _ ms3 (leaves_ok _ _ IN1 CN) HS3 HF3).
  - apply (step_to E (add_cond ah_s0 C_def_lt) ah_s2 _ _ mem md _ Hh Hl HS1' run_s2 ltac:(vm_compute; reflexivity) HF1).
    intros ms2 HS2 HF2. change (st_ok zsegs E ah_s2 ms2) in HS2.
    apply (SR_branch_J zsegs E ah_s2 ms2 md _ BC_EQ (SExt true 32 (SOff 41 0)) (SLit (2^64-1)) HS2); intros _ HS2'.
    + apply (step_to E (add_cond ah_s2 C_cpu_m1) ah_s3 _ _ mem md _ Hh Hl HS2' run_s3 ltac:(vm_compute; reflexivity) HF2).
      intros ms3 HS3 HF3. change (st_ok zsegs E ah_s3 ms3) in HS3.
      apply (SR_branch_J zsegs E ah_s3 ms3 md _ BC_NE (SOff 42 0) (SLit 0) HS3); intros _ HS3'.
      * apply (step_to E (add_cond ah_s3 C_c_set) _ _ _ mem md _ Hh Hl HS3' (run_leaf _ _ IN3 CS) ltac:(vm_compute; reflexivity) HF3).
        intros ms4 HS4 HF4. exact (LEAF _ ms4 (leaves_ok _ _ IN3 CS) HS4 HF4).
      * apply (step_to E (add_cond ah_s3 C_c_null) _ _ _ mem md _ Hh Hl HS3' (run_leaf _ _ IN3 CN) ltac:(vm_compute; reflexivity) HF3).
        intros ms4 HS4 HF4. exact (LEAF _ ms4 (leaves_ok _ _ IN3 CN) HS4 HF4).
    + apply (step_to E (add_cond ah_s2 C_cpu_set) ah_s4 _ _ mem md _ Hh Hl HS2' run_s4 ltac:(vm_compute; reflexivity) HF2).
      intros ms3 HS3 HF3. change (st_ok zsegs E ah_s4 ms3) in HS3.
      apply (SR_branch_J zsegs E ah_s4 ms3 md _ BC_NE (SOff 42 0) (SLit 0) HS3); intros _ HS3'.
      * apply (step_to E (add_cond ah_s4 C_c_set) _ _ _ mem md _ Hh Hl HS3' (run_leaf _ _ IN4 CS) ltac:(vm_compute; reflexivity) HF3).
        intros ms4 HS4 HF4. exact (LEAF _ ms4 (leaves_ok _ _ IN4 CS) HS4 HF4).
      * apply (step_to E (add_cond ah_s4 C_c_null) _ _ _ mem md _ Hh Hl HS3' (run_leaf _ _ IN4 CN) ltac:(vm_compute; reflexivity) HF3).
        intros ms4 HS4 HF4. exact (LEAF _ ms4 (leaves_ok _ _ IN4 CN) HS4 HF4).
Qed.
