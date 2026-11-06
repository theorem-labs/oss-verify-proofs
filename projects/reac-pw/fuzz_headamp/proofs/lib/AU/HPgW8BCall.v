(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the two calls of the
   builder piece W8 of LLVMFuzzerTestOneInput (lib/AU/HPgW8BKit.v), with the premises of each contract discharged
   from the facts the cut J gives: pod_write_ent(pp, &e62) at 0x84634 (`jal` 0x82648) under fuzz_rate's
   image-independent contract PweSpec.pod_write_ent_specX, and __asan_memcpy(&pp->ent[n_ent], &e62, 104) at 0x51d8c
   (`jal` 0x826bc) under the kernel's contract of the intrinsic. Proves no function (kind: segment lemma).

   WHAT THE PREMISES COME FROM. pp is the first block, live and made since the journal's start, so its bytes are the
   journal's to write and the block law gives its alignment, its place in application memory, that its bytes are
   marked usable and that their shadow bytes are readable. e62 is the frame object at F + 0x210 of the class-4 frame
   for locals the harness holds: the frame law gives its alignment, its place and that its bytes and its 128 shadow
   bytes are present, and the frame's shadow pattern at this cut (e62 in scope) gives that its 104 bytes are marked
   usable. R is above the allocator's ceiling and the real frame is below the entry sp, so both callees' stacks lie
   inside the segment's own window [R - 16384, R) and below every byte either call reads or writes. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import PweSpec HPgE0Base HPgW8BKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===================================== geometry ===================================== *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a range of application memory is a range the shadow map covers *)
Lemma hw8_amem : forall p n, in_app p n -> 0 <= n -> amem_range p n.
Proof.
intros p n Happ Hn. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Happ as (H1 & [H2 | (H2 & H3)]);
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *; [left | right]; lia.
Qed.

(* the shadow bytes the two calls read of the frame object e62 lie inside the frame's own 128 shadow bytes *)
Lemma hw8_hull_e62 : forall (H : word -> bool) (mem : word -> option byte) F,
F mod 32 = 0 -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
(forall i, 0 <= i < 128 -> apresent H mem (shadow_addr F + i)) ->
shadow_hull_vis (aview rsegs H mem) (F + 0x210) 104.
Proof.
intros H mem F H32 H0 Hc Hpres s Hs.
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide in H32; [|lia]. destruct H32 as [q Hq]. rewrite Hq.
  replace (q * 32) with ((q * 4) * 8) by ring. apply Z_mod_mult. }
apply (aview_some_of_apresent rsegs).
assert (Hb : shadow_addr F <= s < shadow_addr F + 128).
{ unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. }
replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
apply Hpres. lia.
Qed.
End g.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* what the frame for locals gives at any state of the journal: its alignment and place, its bytes present and its
   128 shadow bytes present *)
Lemma hw8_frame_facts : forall ly S W mem md pos F,
AR rsegs B ly S W mem md -> In (4, pos) (frames S) -> frame_addr ly 4 pos = F ->
F mod 32 = 0 /\ in_app F 1024 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\
(forall a, F <= a < F + 1024 -> apresent (w_H W) mem a) /\
(forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr F + i)).
Proof.
intros ly S W mem md pos F HAR Hin HF.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (al_frames _ _ LAWS ly S W mem md 4 pos HAR Hin) as (Fal & Fapp & Fpres & Fsh).
destruct (frames_bounds rsegs B LAWS ly S W mem md 4 pos HAR Hin) as (F0 & Fc & _).
rewrite HF in Fal, Fapp, Fpres, Fsh, F0, Fc.
change (fs_frame_bytes 4) with 1024 in Fapp, Fpres, Fsh, Fc.
change (1024 / 8) with 128 in Fsh.
split; [exact Fal|]. split; [exact Fapp|]. split; [exact F0|]. split; [exact Fc|].
split; [intros a Ha; exact (proj1 (Fpres a Ha))|].
intros i Hi. exact (proj1 (Fsh i Hi)).
Qed.

(* ===================================== the call of pod_write_ent =====================================
   At 0x84634 with a0 = pp and a1 = &e62: the contract's premises hold, so the call returns at 0x8264c with the
   pod's bytes at buf[len], the len cell at len + |enc_pod ed|, every shadow byte of the application range as at
   the call, and pp's block and e62's bytes still marked usable. *)
Lemma hw8_pwe_step : pod_write_ent_specX rsegs B MT HW8_PWE ->
forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W : world rsegs) memc mdc k (regs : bvmap 5 word)
(R pp F L : Z) (ed : ent) (pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W memc mdc k ->
st_nev S + k <= EV_MAX ->
In (pp, PP_SIZE) (ablocks B ly2 S2) -> ~ In (pp, PP_SIZE) (ablocks B ly S) ->
In (4, pos) (frames S2) -> frame_addr ly2 4 pos = F ->
getr regs 1 = w64 HW8_RA1 -> getr regs 2 = w64 R ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 pp -> getr regs 11 = w64 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + OFF_LEN) 8 L ->
hm_bytes rsegs (w_H W) memc (F + 0x210) (ent_mem ed) ->
hd_fsh rsegs (w_H W) memc F (hmu_sh false false false false false true false false) ->
ent_wf ed -> 0 <= L <= 5384 -> L mod 8 = 0 ->
pp mod 16 = 0 -> in_app pp PP_SIZE -> 4096 <= pp -> pp + PP_SIZE <= alloc_ceiling ->
(pp + PP_SIZE <= F \/ F + 1024 <= pp) ->
alloc_ceiling + T_SEG_STK <= R -> R mod 32 = 0 -> R + 0x220 <= sp0 -> sp0 mod 16 = 0 -> sp0 <= 2 ^ 47 ->
sp0 - STK <= R - T_SEG_STK ->
SRr rsegs W (cfg_at rsegs HW8_PWE regs memc mdc)
(pw_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_pwe_STK regs ly2 S2 W memc mdc
(fun f => f = fx) (pwe_E pp L ed)
(fun W2 _ mem2 =>
garr8 rsegs (mrestrict (w_H W2) mem2) (pp + L) (map (fun x : byte => bv_unsigned x) (enc_pod ed)) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (pp + OFF_LEN) 8 (L + pwe_len ed) /\
(forall x, 0 <= x < kHighMemEnd ->
 aview rsegs (w_H W2) mem2 (shadow_addr x) = aview rsegs (w_H W) memc (shadow_addr x)) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF pp PP_SIZE /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (F + 0x210) ENT_SIZE)).
Proof.
intros PWE STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W memc mdc k regs R pp F L ed pos
HJ Hev Hpp Hfresh Hfr HFa R1 R2 R3 R4 R10 R11 VLEN HEM HFSH Hwf HL HL8 Hpp16 Happ Hpp0 Hppc HpF
HRc HR32 HRsz Hsp16 Hsp47 HSTK.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as Hc47.
assert (HT : T_SEG_STK = 16384) by reflexivity.
assert (HTp : T_pwe_STK = 4144) by reflexivity.
assert (Hrq : req_size PP_SIZE = PP_SIZE) by reflexivity.
destruct (hw8_frame_facts ly2 S2 W memc mdc pos F HAR Hfr HFa) as (HF32 & HFapp & HF0 & HFc & HFpres & HFsh).
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide in HF32; [|lia]. destruct HF32 as [q Hq]. rewrite Hq.
  replace (q * 32) with ((q * 4) * 8) by ring. apply Z_mod_mult. }
assert (Hpp8 : pp mod 8 = 0).
{ apply Z.mod_divide in Hpp16; [|lia]. destruct Hpp16 as [q Hq]. rewrite Hq.
  replace (q * 16) with ((q * 2) * 8) by ring. apply Z_mod_mult. }
assert (HRsp : spZ regs = R) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
(* the pod's size *)
pose proof Hwf as (Hty & Hbody & Hsz).
pose proof (zlen_enc_pod ed Hwf) as Henc.
pose proof (pad8_bound (e_size ed)) as Hpad.
assert (Hpwe : pwe_len ed = 8 + e_size ed + pad8 (e_size ed)) by (unfold pwe_len; exact Henc).
(* the block's shadow facts *)
destruct (hm_blk_ra rsegs B ly2 S2 W memc mdc pp PP_SIZE pp PP_SIZE HAR Hpp ltac:(lia)
  ltac:(rewrite Hrq; lia)) as (HRApp & HHullPp).
(* e62: 104 bytes of the frame, marked usable by the frame's shadow pattern *)
assert (HRAq : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) ENT_SIZE).
{ change ENT_SIZE with 104.
  pose proof (hmu_B_ra_e62 rsegs (w_H W) memc F false false false false false false false 0 104
    HFSH HF8 ltac:(lia) ltac:(lia)) as HR.
  unfold HMU_E62 in HR. replace (F + 0x210) with (F + 0x210 + 0) by lia. exact HR. }
assert (HHullq : shadow_hull_vis (aview rsegs (w_H W) memc) (F + 0x210) ENT_SIZE).
{ change ENT_SIZE with 104. exact (hw8_hull_e62 (w_H W) memc F HF32 HF0 HFc HFsh). }
(* the premises of the contract *)
apply (PWE STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W memc mdc k regs pp (F + 0x210) L ed).
- (* pw_pre *)
  split; [exact HJ|]. split; [rewrite R1; unfold YK0s.ret_ok, w64, HW8_RA1; apply bv_eq; vm_compute; reflexivity|].
  split; [unfold raZ; rewrite R1; unfold w64, HW8_RA1; rewrite unsigned_lit_small by lia; lia|].
  split; [exact R3|]. split; [exact R4|].
  split.
  { rewrite HRsp. apply Z.mod_divide in HR32; [|lia]. destruct HR32 as [q Hq]. rewrite Hq.
    replace (q * 32) with ((q * 2) * 16) by ring. apply Z_mod_mult. }
  split; [rewrite HRsp; lia|]. split; [rewrite HRsp; lia | exact Hev].
- exact R10.
- exact R11.
- lia.
- exact Hpp8.
- unfold PP_SIZE in *. lia.
- apply hw8_amem; [exact Happ | unfold PP_SIZE; lia].
- exact HRApp.
- apply HHullPp. unfold PP_SIZE. lia.
- (* every byte it writes is the journal's own: pp is a block made since the journal's start *)
  apply (pwe_awr_fresh B STK sp0 FP ly S ly2 S2 own pp L ed); [exact Hpp | exact Hfresh | lia |].
  unfold POD_BUF_MAX. lia.
- left. rewrite HRsp. unfold PP_SIZE in *. lia.
- exact VLEN.
- lia.
- exact HL8.
- unfold POD_BUF_MAX. lia.
- lia.
- (* 8 | F + 0x210 *)
  apply Z.mod_divide in HF8; [|lia]. destruct HF8 as [q Hq]. rewrite Hq.
  replace (q * 8 + 0x210) with ((q + 66) * 8) by ring. apply Z_mod_mult.
- apply hw8_amem; [|unfold ENT_SIZE; lia].
  apply (in_app_sub F 1024); [exact HFapp | lia | unfold ENT_SIZE; lia | unfold ENT_SIZE; lia].
- rewrite Hbody. rewrite Z2Nat.id by lia. reflexivity.
- unfold ENT_SIZE. lia.
- exact Hty.
- exact HEM.
- exact HRAq.
- apply HHullq.
- (* pp and e62 are apart *)
  unfold ENT_SIZE, PP_SIZE in *. destruct HpF; [left | right]; lia.
- left. rewrite HRsp. unfold ENT_SIZE in *. lia.
Qed.

(* ===================================== the record copy =====================================
   __asan_memcpy(pp + 0x4014 + 104 n_ent, &e62, 104) at 0x51d8c: the destination is inside the first block (the
   pod loop writes at most 32 records, so the last byte it touches is pp + 0x4d14) and the source is e62. *)
Lemma hw8_cpy_step : aintrin_realizes rsegs B OCpy HW8_MEMCPY ->
forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W : world rsegs) memc mdc k (regs : bvmap 5 word)
(R pp F kk : Z) (pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W memc mdc k ->
In (pp, PP_SIZE) (ablocks B ly2 S2) -> ~ In (pp, PP_SIZE) (ablocks B ly S) ->
In (4, pos) (frames S2) -> frame_addr ly2 4 pos = F ->
getr regs 1 = w64 HW8_RA2 -> getr regs 2 = w64 R ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (pp + 0x4014 + 104 * kk) -> getr regs 11 = w64 (F + 0x210) -> getr regs 12 = w64 104 ->
hd_fsh rsegs (w_H W) memc F (hmu_sh false false false false false true false false) ->
0 <= kk < 32 ->
pp mod 16 = 0 -> in_app pp PP_SIZE -> 4096 <= pp -> pp + PP_SIZE <= alloc_ceiling ->
(pp + PP_SIZE <= F \/ F + 1024 <= pp) ->
alloc_ceiling + T_SEG_STK <= R -> R mod 32 = 0 -> R + 0x220 <= sp0 -> sp0 mod 16 = 0 -> sp0 <= 2 ^ 47 ->
sp0 - STK <= R - T_SEG_STK ->
SRr rsegs W (cfg_at rsegs HW8_MEMCPY regs memc mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (w64 HW8_RA2) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regs regs2 /\ getr regs2 10 = w64 (pp + 0x4014 + 104 * kk) /\
(forall i, 0 <= i < 104 ->
 aview rsegs (w_H W) mem2 (pp + 0x4014 + 104 * kk + i) = aview rsegs (w_H W) memc (F + 0x210 + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 0x4014 + 104 * kk <= a < pp + 0x4014 + 104 * kk + 104) ->
 ~ (R - ESTACK <= a < R) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros ACPY STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W memc mdc k regs R pp F kk pos
HJ Hpp Hfresh Hfr HFa R1 R2 R3 R4 R10 R11 R12 HFSH Hkk Hpp16 Happ Hpp0 Hppc HpF
HRc HR32 HRsz Hsp16 Hsp47 HSTK.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as Hc47.
assert (HT : T_SEG_STK = 16384) by reflexivity.
assert (HE : ESTACK = 4096) by reflexivity.
assert (Hrq : req_size PP_SIZE = PP_SIZE) by reflexivity.
destruct (hw8_frame_facts ly2 S2 W memc mdc pos F HAR Hfr HFa) as (HF32 & HFapp & HF0 & HFc & HFpres & HFsh).
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide in HF32; [|lia]. destruct HF32 as [q Hq]. rewrite Hq.
  replace (q * 32) with ((q * 4) * 8) by ring. apply Z_mod_mult. }
assert (HRsp : spZ regs = sp0 + (R - sp0)) by (unfold spZ; rewrite R2; rewrite unsigned_lit_small by lia; lia).
destruct (hm_blk_ra rsegs B ly2 S2 W memc mdc pp PP_SIZE (pp + 0x4014 + 104 * kk) 104 HAR Hpp ltac:(lia)
  ltac:(rewrite Hrq; unfold PP_SIZE; lia)) as (HRAd & HHulld).
assert (HRAq : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104).
{ pose proof (hmu_B_ra_e62 rsegs (w_H W) memc F false false false false false false false 0 104
    HFSH HF8 ltac:(lia) ltac:(lia)) as HR.
  unfold HMU_E62 in HR. replace (F + 0x210) with (F + 0x210 + 0) by lia. exact HR. }
eapply SRr_mono.
{ apply (e0_memcpy_at B LAWS ACPY W regs memc STK sp0 FP ly S W0 mem0 md0 own ly2 S2 mdc k
    (pp + 0x4014 + 104 * kk) (F + 0x210) 104 (R - sp0) (w64 HW8_RA2) HJ R10 R11 R12).
  - lia.
  - unfold PP_SIZE in *. lia.
  - unfold PP_SIZE in *. lia.
  - exact HRsp.
  - apply Z.mod_divide in HR32; [|lia]. destruct HR32 as [q Hq].
    rewrite Zminus_mod, Hq, Hsp16, Z.sub_0_r, Z.mod_mod by lia.
    replace (q * 32) with ((q * 2) * 16) by ring. apply Z_mod_mult.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - unfold YK0s.ret_ok, w64, HW8_RA2. apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (pp + (a - pp)) by lia.
      apply (hd_fresh_awr STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own pp PP_SIZE);
        [exact Hpp | exact Hfresh | rewrite Hrq; unfold PP_SIZE in *; lia].
    + unfold PP_SIZE in *. lia.
  - apply hw8_amem; [|lia].
    apply (in_app_sub pp PP_SIZE); [exact Happ | lia | lia | unfold PP_SIZE in *; lia].
  - exact HRAd.
  - intros _. apply HHulld. lia.
  - lia.
  - unfold ENT_SIZE in *. lia.
  - (* the source bytes are present and below the callee's stack *)
    intros a Ha. split.
    + apply (aview_some_of_apresent rsegs). apply HFpres. lia.
    + rewrite HRsp. unfold ESTACK in *. lia.
  - unfold PP_SIZE in *. destruct HpF; [left | right]; lia.
  - apply hw8_amem; [|lia].
    apply (in_app_sub F 1024); [exact HFapp | lia | lia | lia].
  - exact HRAq.
  - intros _. exact (hw8_hull_e62 (w_H W) memc F HF32 HF0 HFc HFsh). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc & HJ2 & Hio & Hpres & H10 & Hcpy & Hkeep & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact Hio|]. split; [exact Hpres|]. split; [exact H10|].
split; [exact Hcpy|].
split; [intros a Ha H1 H2; apply Hkeep; [exact Ha | exact H1 | lia] | exact Hpres2].
Qed.
End b.

Print Assumptions hw8_amem.
Print Assumptions hw8_hull_e62.
Print Assumptions hw8_frame_facts.
Print Assumptions hw8_pwe_step.
Print Assumptions hw8_cpy_step.
