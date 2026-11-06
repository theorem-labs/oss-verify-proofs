(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the journal rule of a call to the stack-frame release entry (aj_stack_free_at of proofs/cgif/cgif_rgb_fuzzer/lib/YC05.v) and the write rule it uses (ajournal_after_write_win of that file), restated over the journal of the cgif_file_fuzzer proof (YCbq.ajournal) as libreac/fuzz_grant holds it; module names. The released shadow span is sf_span cid n (StackFreeDef.v), not n / 8. The rule has no frame_flag_law hypothesis: the facts it needs about the frame's flag byte (owned, an application address, outside the image) come from AR_laws (al_flag, al_client_img). *)
(* Modified by Theorem Labs, 2026-10: copied by path from libreac/fuzz_grant (a working branch 16327857853; the same text as a working branch c3bfa00452c) with only the module prefix changed to libreac.fuzz_disco. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Reusable/StackFreeJournal.v, with its module paths and module names changed; 698 of its 821 lines of code are new or changed and 116 lines of the source are left out. *)
(* The walk of LLVMFuzzerTestOneInput's exit phase X (fuzz_boxreg.asan 0x80e14 .. the `ret` at 0x80f5c) on the
   ASan build, from the cut GI_X of BoxLxDefs.v to the post-condition gb_post of the whole call.

   0x80e14  mv a0, s4; jal free           free (r): the table, the call's own block (afree04_rule, trace site 0xed0)
   0x80e1c  ld s6, 0x18(s1); ld a4, 0x28(s1)   both slots hold the side-stack frame F
   0x80e24  a0 = 0x45e0360e; sd a0, 0(a4)       the retired-frame magic into F's first word
   0x80e30  beqz s6                              not taken: F >= 4096
   0x80e34  a1 = 0x40; a0 = s8; jal __asan_set_shadow_f5   F's 64 shadow bytes := 0xf5 (aset_shadow_realizes)
   0x80e40  ld a0, 0x1f8(s6); sb zero, 0(a0)    the slot's flag byte := 0: the frame is given back
                                                 (BoxFrame.v aj_flag_store_pi, astack_free_law, frame_flag_lawP)
   0x80f1c  a0 = 0; sp = s0; ra, s0 .. s11 read back from the saved words; ret

   The phase is cut after each call: GI_XA at 0x80e1c (free has returned), GI_XB at 0x80e40 (the shadow is
   poisoned); each segment lemma has the shape `gb_from POST G_next -> gb_from POST G_self`, and the last one ends
   at the caller's return address in gb_post. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05 YG0s YG0p.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxAddr BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC4b BoxFrame ReacBoxregInit BoxLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SetShadowDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lib/Reusable/YCbq.v's zlia, under this file's name (a later import shadows that name). *)
Local Ltac zlia := unfold app_addr, in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg,
  kHighMemEnd, kHighShadowEnd, kImgLo in *; lia.

(* ---- the pcs of the cuts (offsets from 0x7ff4c) and the engine's states ---- *)
Definition GX_A : Z := 0xed0.     (* 0x80e1c: free (r) has returned                   *)
Definition GX_B : Z := 0xef4.     (* 0x80e40: __asan_set_shadow_f5 has returned        *)
(* The shadow-check runner's parameters: no shadow load is on this path, so the span is a point no window meets. *)
Definition GX_Bx : sv := SLit 0x7fff8000.
Definition GX_span : Z * Z := (0, 0).
(* 0x80e1c: the two spill slots that name F (atom 32), and F's first word, which the magic store writes. *)
Definition GX_sl : YP09.region := YP09.mkRegion (Some 9%nat) 0x18 0x30 0 0
  [YP09.mkChunk 0x18 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x28 (CVal 8 (SOff 32 0))].
Definition GX_F : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [].
(* 0x80e40: the saved words at s0 = the caller's sp (atoms 33 .. 45: ra, s0, s1, s2 .. s11 of the caller), the
   flag word at F + 504 (s6, atom 32 = the flag address), and the flag byte, which the store writes. *)
Definition GX_svc : list YP09.chunk :=
  [ YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 45 0)) ].
Definition GX_sv : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 GX_svc.
Definition GX_FW : YP09.region := YP09.mkRegion (Some 22%nat) 504 512 0 0 [YP09.mkChunk 504 (CVal 8 (SOff 32 0))].
Definition GX_FL : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition gx_ssA : sstate := mkSS GP_X sr_atoms [] None (mkFacts [] [] []).
Definition gx_ssB : sstate := mkSS GX_A sr_atoms [GX_sl; GX_F] None (mkFacts [(32%nat, mkAF 4096 (2 ^ 47) 0)] [] []).
Definition gx_ssC : sstate := mkSS GX_B sr_atoms [GX_sv; GX_FW; GX_FL] None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

(* The value of the caller's register s<j> (x8, x9, x18 .. x27), as the saved word gsaved names it. *)
Definition gsv (cx : bcx) (j : Z) : Z := bv_unsigned (getr (c_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))).
(* The extra atoms of the last segment: 32 the flag address, 33 the caller's ra, 34 .. 45 its s0 .. s11. *)
Definition gx_xs (cx : bcx) (fp : Z) : list word :=
  [ Z_to_bv 64 (gFL cx fp); Z_to_bv 64 (raZ (c_regs cx));
    Z_to_bv 64 (gsv cx 0); Z_to_bv 64 (gsv cx 1); Z_to_bv 64 (gsv cx 2); Z_to_bv 64 (gsv cx 3);
    Z_to_bv 64 (gsv cx 4); Z_to_bv 64 (gsv cx 5); Z_to_bv 64 (gsv cx 6); Z_to_bv 64 (gsv cx 7);
    Z_to_bv 64 (gsv cx 8); Z_to_bv 64 (gsv cx 9); Z_to_bv 64 (gsv cx 10); Z_to_bv 64 (gsv cx 11) ].

Lemma gx_mkst : forall (ms : machine_state) pc,
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS).
Proof.
intros [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0] pc.
cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem].
intros -> -> -> -> -> ->. reflexivity.
Qed.

(* A saved word as a chunk of a region. *)
Lemma gx_chunk_word : forall E (H : word -> bool) m base off n v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H m) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E H m base off n v He Hv Hr.
apply (chunk_ok_val SEGS E _ base off 8 (SOff n 0) v).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact He.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn. lia.
- change (N.to_nat 8) with 8%nat. exact (val_mem_of_rdword SEGS H m _ _ Hr).
Qed.

(* Two memories that hold the same byte list at base agree there. *)
Lemma gx_input_eq : forall (H H' : word -> bool) m m' base (l : list Z) i,
  garr8 SEGS (mrestrict H m) base l -> garr8 SEGS (mrestrict H' m') base l ->
  0 <= i < Z.of_nat (length l) -> aview SEGS H m (base + i) = aview SEGS H' m' (base + i).
Proof.
intros H H' m m' base l i G1 G2 Hi. unfold aview.
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (garr8_mbyte SEGS _ _ _ (Z.to_nat i) G1 ltac:(lia)), (garr8_mbyte SEGS _ _ _ (Z.to_nat i) G2 ltac:(lia)).
reflexivity.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASETF5 : aset_shadow_realizes SEGS B (SIGMA BS___asan_set_shadow_f5) 0xf5.

(* ---- the cuts of the phase ---- *)
(* 0x80e1c: free (r) has returned; the blocks are the caller's again. *)
Definition GI_XA (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  gb_body cx fp GX_A W3 ms3 GSH_J /\ k <= 130 /\ acc <= GB_NEED MT /\
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)).
(* 0x80e40: the frame's shadow is poisoned; s6 holds F. *)
Definition GI_XB (cx : bcx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + GX_B) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  gregs cx fp ms3 /\ getr (ms_regs ms3) 22 = w64 (gF cx fp) /\ gsaved cx W3 ms3 /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  k <= 130 /\ acc <= GB_NEED MT /\
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)).

(* ---- the geometry every segment runs in ---- *)
Lemma gx_geo : forall cx fp k ly3 S3 W3 mem3 md3,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  frames S3 = [(GB_CID, fp)] ->
  (alloc_ceiling + GB_STK <= spZ (c_regs cx) <= 2 ^ 47 /\ spZ (c_regs cx) mod 16 = 0 /\
   spZ (c_regs cx) - 288 < c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0) /\
  (frame_addr ly3 GB_CID fp = gF cx fp /\ flag_addr ly3 GB_CID fp = gFL cx fp /\
   fs_frame_bytes GB_CID = 512 /\ gSH cx fp = shadow_addr (gF cx fp)) /\
  (4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) /\
  (4096 <= gFL cx fp < alloc_ceiling /\ apresent (w_H W3) mem3 (gFL cx fp) /\ aowned B ly3 S3 (gFL cx fp) /\
   ~ in_img SEGS (gFL cx fp)) /\
  (forall a, gF cx fp <= a < gF cx fp + 512 -> apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W3) mem3 (gSH cx fp + i) /\ ~ aowned B ly3 S3 (gSH cx fp + i)).
Proof.
intros cx fp k ly3 S3 W3 mem3 md3 HB HJ HFR.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (EF : frame_addr ly3 GB_CID fp = gF cx fp) by (unfold gF, frame_addr; rewrite HlyF; reflexivity).
assert (EFL : flag_addr ly3 GB_CID fp = gFL cx fp) by (unfold gFL, flag_addr; rewrite HlyF; reflexivity).
assert (Hfb : fs_frame_bytes GB_CID = 512) by reflexivity.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF0 & HFc & HFia).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (_ & _ & Hfrb & Hfsh).
destruct (FFL _ _ _ _ _ _ _ HAR Hfin) as (HFLp & HFLo & (_ & HFLimg) & (HFL0 & _ & HFLc)).
rewrite ?EF, ?Hfb in HF0, HFc, HFia, Hfrb, Hfsh. rewrite ?EFL in HFLp, HFLo, HFLimg, HFL0, HFLc.
assert (ESH : gSH cx fp = shadow_addr (gF cx fp)) by reflexivity.
pose proof (Z.div_mod (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hmp.
unfold GB_STK in *.
split; [split; [lia|]; split; [exact Hal16|]; split; [rewrite Hsp1; lia | rewrite Hsp1, Z.mul_comm, Z_mod_mult; reflexivity]|].
split; [split; [exact EF|]; split; [exact EFL|]; split; [exact Hfb | exact ESH]|].
split; [split; [exact HF0|]; split; [exact HFc | exact HFia]|].
split; [split; [lia|]; split; [exact HFLp|]; split; [exact HFLo | exact HFLimg]|].
split; [exact Hfrb|].
intros i Hi. rewrite ESH. change (512 / 8) with 64 in Hfsh. exact (Hfsh i Hi).
Qed.

(* The call chain at the realigned stack pointer, seen through a phase's layout (cgif lib/A/ACf5.v:172). *)
Lemma gx_achain : forall cx ly3 (rd' : reader) sp',
  gb_base B MT cx -> ly_top ly3 = ly_top (c_ly cx) ->
  (forall a, spZ (c_regs cx) <= a < 2 ^ 64 -> rd' a = aview SEGS (w_H (c_W cx)) (c_mem cx) a) ->
  rdword rd' (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword rd' (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain ly3 rd' sp' (spZ (c_regs cx)) (gch cx).
Proof.
intros cx ly3 rd' sp' HB Etop Hk H8 H16 Hsp'.
apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
destruct HB as (HPRE & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hal8 : spZ (c_regs cx) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia].
  destruct Hal16 as [q Hq]. exists (2 * q). lia. }
unfold gch.
destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
- apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) rd'
           (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] sp' Hch ltac:(lia) Hk H8 H16 Hra4);
    [lia | exact Hal8 | lia | exact Hsp'].
- left. split; [right; left; lia | reflexivity].
Qed.

(* ---- a write the journal allows: fuzz_identity's ajournal_after_write_win (cgif_rgb lib/YC05.v), whose presence
   premise speaks only of the stack window, on this tree's journal (lib/Reusable/YCbq.v ajournal_after_write) ---- *)
Lemma gx_after_write_win : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img SEGS a)) ->
AR SEGS B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal SEGS B STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
(~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img SEGS a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx]; [left; exact (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]) | (_ & Hx)]; [exact (Hs Hs') | zlia | zlia | zlia | zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx)].
- zlia.
- exact (Hnf Hfp).
-
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
- zlia.
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo). }
split.
{
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (pa_segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx & Hxi)].
- zlia.
- exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (fs_frame_bytes_nonneg cid) as Hnn0.
assert (Hb0 : 0 <= frame_addr lyc cid pos < kHighMemEnd) by zlia.
assert (Hb1 : 0 <= frame_addr lyc cid pos + fs_frame_bytes cid < kHighMemEnd) by zlia.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) Hb0) as Hsb1.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) Hb1) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn0) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
- zlia.
- destruct Hr as [Hr | Hr]; [|zlia].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (sep_frames_pos SEGS B LAWS lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
pose proof (fs_frame_bytes_nonneg c') as Hnn'.
destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
+ destruct Hr as [Hr | Hr]; [zlia | zlia].
+ destruct Hr as [Hr | Hr]; [zlia |].
destruct Hd as [Hd | Hd].
* pose proof (shadow_mono _ _ Hd). zlia.
* pose proof (shadow_mono _ _ Hd). zlia.
-
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by zlia.
exact (proj2 Hfsh Hxo). }
split; [exact Hgone|].
split; [intros a Ha; apply (Hgr a Ha); apply Hpres, Ha|].
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (AR_extra_law_ok SEGS B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as [(_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]])]]) | (Hxo & Hx)].
- apply Xs. rewrite Eslo, Eshi. zlia.
- exact (Xb b m Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
- exact (Xo Hxo). }
Qed.

(* ---- the call of __asan_set_shadow_f5 on a frame the journal owns: fuzz_identity's aj_set_shadow_at
   (cgif_rgb lib/YC05.v) on this tree's journal; the one place that reads ASETF5 ---- *)
Lemma gx_set_shadow : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  In (cid, pos) own ->
  getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
  shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BS___asan_set_shadow_f5)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\
    (forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (q + i) = Some 0xf5) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
  HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASETF5 lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hoff : forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a).
{ intros a Ha Hni Hp. destruct (Z_le_gt_dec q a) as [Hqa|Hqa]; [destruct (Z_lt_ge_dec a (q + n)) as [Han|Han]|].
  - specialize (Heff (a - q) ltac:(lia)). replace (q + (a - q)) with a in Heff by lia.
    destruct Hp as [Hh _]. split; [exact Hh|]. unfold aview, mbyte, mrestrict in Heff. rewrite Hh in Heff.
    destruct (mem2 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso.
    rewrite (seg_rom_none SEGS a Ha Hni) in Heff. discriminate.
  - eapply (apresent_transfer SEGS); [exact Ha | exact Hni | apply Hfr; [exact Ha | lia] | exact Hp].
  - eapply (apresent_transfer SEGS); [exact Ha | exact Hni | apply Hfr; [exact Ha | lia] | exact Hp]. }
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (gx_after_write_win STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => q <= a < q + n) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha Hna).
  - intros a Ha Hp. apply Hoff; [zlia | intros Hi; pose proof (pa_segs_low a Hi); zlia | exact Hp].
  - exact Hsame.
  - intros a Ha. left. right. right. right. exists cid, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact Heff | exact Hfr].
Qed.

(* The caller's input bytes: an application block the phase holds, owned by nobody, off the frames. *)
Lemma gx_input_blk : forall cx ly3 S3 W3 mem3 md3,
  gb_base B MT cx -> AR SEGS B ly3 S3 W3 mem3 md3 ->
  (forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3)) ->
  forall a, c_p cx <= a < c_p cx + c_n cx ->
  4096 <= a < alloc_ceiling /\ apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a /\ app_addr a /\
  (forall cid pos, In (cid, pos) (frames S3) -> ~ (frame_addr ly3 cid pos <= a < frame_addr ly3 cid pos + fs_frame_bytes cid)).
Proof.
intros cx ly3 S3 W3 mem3 md3 HB HAR Hsub a Ha.
pose proof HB as (_ & _ & _ & Hpn & _).
destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
specialize (Hsub _ Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hsub) as (_ & H4096 & Hceil & Hia & Hpres & _).
pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
destruct (Hpres a ltac:(lia)) as [Hp Ho].
split; [lia|]. split; [exact Hp|]. split; [exact Ho|]. split; [exact (in_app_addr _ _ a Hia ltac:(lia))|].
intros cid pos Hf Hr. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ cid pos HAR Hsub Hf) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma gx_bvr : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.

Lemma gx_rd_tr : forall (rd rd' : reader) a v,
  (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk Hr. rewrite (rdword_ext rd rd' a Hk). exact Hr. Qed.

Lemma gx_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [x Hx]. destruct Hb as [y Hy]. exists (2 * x - y). lia.
Qed.

(* The frame's 64 shadow bytes lie off every application address, and off the frame. *)
Lemma gx_shadow_sep : forall F, 4096 <= F -> F + 512 <= alloc_ceiling -> in_app F 512 ->
  (forall a, app_addr a -> ~ (shadow_addr F <= a < shadow_addr F + 64)) /\
  (forall a, F <= a < F + 512 -> ~ (shadow_addr F <= a < shadow_addr F + 64)) /\
  shadow_addr F + 64 <= alloc_ceiling.
Proof.
intros F H0 Hc Hia. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod F 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as Hm.
unfold shadow_addr, SHADOW_OFF. split; [|split].
- intros a Ha. zlia.
- intros a Ha. zlia.
- zlia.
Qed.

(* ---- 0x80e40 .. the `ret` at 0x80f5c: the flag byte, the epilogue, the return ---- *)
Theorem gx_seg_ret : gb_from B MT (gb_post B MT) GI_XB.
Proof.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & G22 &
  (Sra & Ssv) & HFLW & HIN & Hk & Hacc & HPerm).
pose proof HB as (HPRE & _ & _ & Hpn & Hgarr0 & _ & Hev & _ & _ & _ & _ & _ & _ & HMOK & _ & HNEED).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & _).
destruct (gx_geo cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ HFR) as
  ((Hsp & Hal16 & Hsp1 & Hsp32) & (EF & EFL & Hfb & ESH) & (HF0 & HFc & HFia) & (HFL & HFLp & HFLo & HFLimg) & HFRB & _).
pose proof HJ as (HAR3 & _).
assert (HFLnF : ~ (gF cx fp <= gFL cx fp < gF cx fp + 512)) by (intros Hx; exact (proj2 (HFRB _ Hx) HFLo)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold GB_STK in Hsp.
rewrite (gx_mkst ms3 GX_B Hpc Hresv Hsvc Hrom Hfrg Hfcsr).
remember (Eimg (Ereg (ms_regs ms3) (gx_xs cx fp))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (gx_xs cx fp) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (F32 : ew E 32 = Z_to_bv 64 (gFL cx fp)) by exact (EX 0%nat ltac:(lia)).
assert (F33 : ew E 33 = Z_to_bv 64 (raZ (c_regs cx))) by exact (EX 1%nat ltac:(lia)).
assert (F34 : ew E 34 = Z_to_bv 64 (gsv cx 0)) by exact (EX 2%nat ltac:(lia)).
assert (F35 : ew E 35 = Z_to_bv 64 (gsv cx 1)) by exact (EX 3%nat ltac:(lia)).
assert (F36 : ew E 36 = Z_to_bv 64 (gsv cx 2)) by exact (EX 4%nat ltac:(lia)).
assert (F37 : ew E 37 = Z_to_bv 64 (gsv cx 3)) by exact (EX 5%nat ltac:(lia)).
assert (F38 : ew E 38 = Z_to_bv 64 (gsv cx 4)) by exact (EX 6%nat ltac:(lia)).
assert (F39 : ew E 39 = Z_to_bv 64 (gsv cx 5)) by exact (EX 7%nat ltac:(lia)).
assert (F40 : ew E 40 = Z_to_bv 64 (gsv cx 6)) by exact (EX 8%nat ltac:(lia)).
assert (F41 : ew E 41 = Z_to_bv 64 (gsv cx 7)) by exact (EX 9%nat ltac:(lia)).
assert (F42 : ew E 42 = Z_to_bv 64 (gsv cx 8)) by exact (EX 10%nat ltac:(lia)).
assert (F43 : ew E 43 = Z_to_bv 64 (gsv cx 9)) by exact (EX 11%nat ltac:(lia)).
assert (F44 : ew E 44 = Z_to_bv 64 (gsv cx 10)) by exact (EX 12%nat ltac:(lia)).
assert (F45 : ew E 45 = Z_to_bv 64 (gsv cx 11)) by exact (EX 13%nat ltac:(lia)).
assert (U8 : bv_unsigned (ew E 8) = spZ (c_regs cx))
  by (rewrite (EE 8%nat 8%bv eq_refl), G8; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = gF cx fp)
  by (rewrite (EE 22%nat 22%bv eq_refl), G22; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = gFL cx fp) by (rewrite F32; apply unsigned_lit_small; lia).
(* The engine's state at 0x80e40: the saved words, the flag word, the flag byte. *)
assert (HS : st_ok_pi SEGS VAL E gx_ssC
  (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GX_B)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold gx_ssC. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold GX_sv, YP09.region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U8.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold GX_svc.
      apply Forall_cons.
      { apply (gx_chunk_word E _ _ _ _ 33 (raZ (c_regs cx)) F33 (gx_bvr _)).
        etransitivity; [|exact Sra]. f_equal; try lia. }
      Local Ltac gx_svj Ssv F j :=
        apply Forall_cons;
        [ apply (gx_chunk_word _ _ _ _ _ _ _ F (gx_bvr _));
          etransitivity; [|exact (Ssv j ltac:(lia))]; f_equal; try lia | ].
      gx_svj Ssv F34 0. gx_svj Ssv F35 1. gx_svj Ssv F36 2. gx_svj Ssv F37 3. gx_svj Ssv F38 4. gx_svj Ssv F39 5.
      gx_svj Ssv F40 6. gx_svj Ssv F41 7. gx_svj Ssv F42 8. gx_svj Ssv F43 9. gx_svj Ssv F44 10. gx_svj Ssv F45 11.
      apply Forall_nil.
    + unfold GX_FW, YP09.region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U22.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (gx_chunk_word E _ _ _ _ 32 (gFL cx fp) F32 ltac:(lia)).
      etransitivity; [|exact HFLW]. f_equal. rewrite Hfb. lia.
    + unfold GX_FL, YP09.region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U32.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (gFL cx fp + o) with (gFL cx fp) by lia. exact (apresent_writable SEGS _ _ _ HFLp).
  - unfold GX_sv, GX_FW, GX_FL.
    cbn [YP09.pairwise_disjoint YP09.all_disjoint].
    unfold YP09.extent_disjoint, YP09.base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U8, U22, U32. repeat split; lia.
  - split; [exact I | split; exact I]. }
pose proof (aj_flag_store_pi B LAWS ML ASF FFL) as RUNF.
paj_run_flag_sh RUNF HS HJ.
{ unfold GB_CID. lia. }
{ intros a (rg & Hrg & Hb). unfold gx_ssC in Hrg. cbn [ss_mem In] in Hrg.
  destruct Hrg as [<- | [<- | [<- | []]]];
    unfold GX_sv, GX_FW, GX_FL in Hb; cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; [lia | lia |].
  right. rewrite U32 in Hb. rewrite EFL. lia. }
{ intros msr HS'. pose proof (st_ok_pi_region_nth E _ msr 2 _ HS' eq_refl) as HR.
  destruct HR as (_ & _ & _ & HC).
  cbn [YP09.r_chunks YP09.r_base YP09.base_val] in HC. apply Forall_inv in HC.
  destruct (HC 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. rewrite U32 in Hb2.
  rewrite EFL. replace (gFL cx fp) with (gFL cx fp + 0 + 0) by lia. rewrite Hb2. f_equal.
  injection Hb1 as <-. apply bv_eq. vm_compute. reflexivity. }
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
pose proof (paj_ret_at (PL := PL_box) (PI := PI)) as RET.
eapply (RET W3 E _ msF _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat2.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10.
prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25.
prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
unfold gb_post.
refine (ex_intro _ ly3 (ex_intro _ (stack_free_state GB_CID fp S3) (ex_intro _ (ms_regs msF)
  (ex_intro _ (ms_mem msF) (ex_intro _ _ (ex_intro _ k _)))))).
split.
{ rewrite R1, F33. unfold raZ. rewrite Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [eapply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split; [unfold GB_EV; lia|].
split.
{ apply aregs_preserved_eqs.
  - rewrite R2, (EE 8%nat 8%bv eq_refl), G8. unfold w64, spZ. apply Z_to_bv_bv_unsigned.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact G3.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact G4.
  - rewrite R8, F34. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R9, F35. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R18, F36. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R19, F37. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R20, F38. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R21, F39. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R22, F40. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R23, F41. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R24, F42. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R25, F43. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R26, F44. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite R27, F45. unfold gsv. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact R10|].
split; [exact HPerm|].
split.
{ unfold stack_free_state. apply (mo_le_set_fs_r MT MTF). apply (mle_weaken MT _ _ acc _ MTL HMO). lia. }
assert (Hsub : forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
assert (GIN : garr8 SEGS (mrestrict (w_H W3) (ms_mem msF)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx))).
{ apply (garr8_frame SEGS _ _ _ _ HIN). intros a Ha. rewrite length_map in Ha.
  destruct (gx_input_blk cx ly3 S3 W3 (ms_mem ms3) md3 HB HAR3 Hsub a ltac:(unfold c_n; lia)) as (Ha0 & _ & Hao & _).
  unfold mbyte. cbn [ms_mem mkst] in HFr. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (rg & Hrg & Hb). unfold gx_ssC in Hrg. cbn [ss_mem In] in Hrg.
  destruct Hrg as [<- | [<- | [<- | []]]];
    unfold GX_sv, GX_FW, GX_FL in Hb; cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; [lia | lia |].
  rewrite U32 in Hb. assert (a = gFL cx fp) by lia. subst a. exact (Hao HFLo). }
intros i Hi.
exact (gx_input_eq (w_H W3) (w_H (c_W cx)) (ms_mem msF) (c_mem cx) (c_p cx) _ i GIN Hgarr0
  ltac:(rewrite length_map; unfold c_n in Hi; lia)).
Qed.

(* ---- 0x80e1c .. 0x80e40: the two frame slots, the magic word, `beqz s6` not taken, __asan_set_shadow_f5 ---- *)
Theorem gx_seg_shadow : forall POST, gb_from B MT POST GI_XB -> gb_from B MT POST GI_XA.
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (HBODY & Hk & Hacc & HPerm).
destruct HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & (G2 & G8 & G9 & G3 & G4 & G18 & G24) &
  (Sra & Ssv) & HSH & Hlen & HFLW & (L18 & L28 & _ & _ & _) & HIN).
pose proof HB as (HPRE & _ & _ & Hpn & _ & _ & Hev & _ & _ & _ & _ & _ & _ & HMOK & _ & HNEED).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & _).
destruct (gx_geo cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ HFR) as
  ((Hsp & Hal16 & Hsp1 & Hsp32) & (EF & EFL & Hfb & ESH) & (HF0 & HFc & HFia) & (HFL & HFLp & HFLo & HFLimg) & HFRB & _).
pose proof HJ as (HAR3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
unfold GB_STK in Hsp.
destruct (gx_shadow_sep (gF cx fp) HF0 HFc HFia) as (SHapp & SHfr & SHc). rewrite <- ESH in SHapp, SHfr, SHc.
assert (Hsub : forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
rewrite (gx_mkst ms3 GX_A Hpc Hresv Hsvc Hrom Hfrg Hfcsr).
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (gF cx fp)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (F32 : ew E 32 = Z_to_bv 64 (gF cx fp))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), G9; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = gF cx fp) by (rewrite F32; apply unsigned_lit_small; lia).
(* The engine's state at 0x80e1c: the two slots that name F, and F's first word. *)
assert (HS : st_ok_pi SEGS VAL E gx_ssB
  (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GX_A)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold gx_ssB. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold GX_sl, YP09.region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (gx_chunk_word E _ _ _ _ 32 (gF cx fp) F32 ltac:(lia)). exact L18.
      * apply (gx_chunk_word E _ _ _ _ 32 (gF cx fp) F32 ltac:(lia)). exact L28.
    + unfold GX_F, YP09.region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U32.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFRB (gF cx fp + o) ltac:(lia))).
  - unfold GX_sl, GX_F.
    cbn [YP09.pairwise_disjoint YP09.all_disjoint].
    unfold YP09.extent_disjoint, YP09.base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U9, U32. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U32. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
assert (SHOK : sh_ok SEGS GX_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
pose proof (paj_run B LAWS) as RUN.
paj_run_tok RUN HS HJ SHOK GX_span.
{ intros a (rg & Hrg & Hb). unfold gx_ssB in Hrg. cbn [ss_mem In] in Hrg.
  destruct Hrg as [<- | [<- | []]]; unfold GX_sl, GX_F in Hb;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; [lia|].
  rewrite U32 in Hb. right. right. right. exists GB_CID, fp. split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms1 end.
(* The run wrote only F's first word. *)
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (gF cx fp <= a < gF cx fp + 8) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn.
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ms1)) |- _ =>
    cbn [ms_mem mkst] in HFx;
    apply (kept_of_frame E _ (w_H W3) _ _ (fun x => gF cx fp <= x < gF cx fp + 8) HFx); [|exact Ha | exact Hn] end.
  intros b wlo whi x Hin Hx. unfold gx_ssB, GX_sl, GX_F in Hin. cbn [ss_mem windows map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [YP09.base_val] in Hx; [lia | rewrite U32 in Hx; lia]. }
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. rewrite (EE 2%nat 2%bv eq_refl) in Q2.
prreg HS (3%bv : bv 5) Q3. rewrite (EE 3%nat 3%bv eq_refl) in Q3.
prreg HS (4%bv : bv 5) Q4. rewrite (EE 4%nat 4%bv eq_refl) in Q4.
prreg HS (8%bv : bv 5) Q8. rewrite (EE 8%nat 8%bv eq_refl) in Q8.
prreg HS (9%bv : bv 5) Q9. rewrite (EE 9%nat 9%bv eq_refl) in Q9.
prreg HS (10%bv : bv 5) Q10. rewrite (EE 24%nat 24%bv eq_refl) in Q10.
prreg HS (11%bv : bv 5) Q11.
prreg HS (18%bv : bv 5) Q18. rewrite (EE 18%nat 18%bv eq_refl) in Q18.
prreg HS (22%bv : bv 5) Q22. rewrite F32 in Q22.
prreg HS (24%bv : bv 5) Q24. rewrite (EE 24%nat 24%bv eq_refl) in Q24.
assert (Usp : spZ (ms_regs ms1) = c_sp1 cx) by (unfold spZ; rewrite Q2, G2; unfold w64; apply unsigned_lit_small; lia).
pmkst HS.
eapply SRr_bind.
{ eapply (gx_set_shadow W3 (ms_regs ms1) (ms_mem ms1) GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k GB_CID fp (gSH cx fp) 64 (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + GX_B)) HJ).
  - left. reflexivity.
  - rewrite Q10. exact G24.
  - rewrite Q11. reflexivity.
  - lia.
  - rewrite EF, ESH. lia.
  - rewrite EF, ESH, Hfb. change (512 / 8) with 64. lia.
  - rewrite Usp. lia.
  - exact (gx_mod16 _ _ Hsp32 Hal16).
  - lia.
  - unfold GB_STK. assert (ESTACK = 4096) as Hes by reflexivity. lia.
  - rewrite Q3, G3. exact Hgp.
  - rewrite Q4, G4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold GX_B; lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsh & Hkeep).
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms1) r).
{ intros r Hr. pose proof (HP2 (bv_unsigned r) Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (gSH cx fp <= a < gSH cx fp + 64) -> ~ (gF cx fp <= a < gF cx fp + 8) ->
  aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha H1 H2. rewrite (Hkeep a Ha H1). exact (M1 a Ha H2). }
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + GX_B)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
unfold GI_XB, gregs, gsaved. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{ split; [rewrite (KP 2%bv ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)), Q2; exact G2|].
  split; [rewrite (KP 8%bv ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)), Q8; exact G8|].
  split; [rewrite (KP 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)), Q9; exact G9|].
  split; [rewrite (KP 3%bv ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)), Q3; exact G3|].
  split; [rewrite (KP 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), Q4; exact G4|].
  split; [rewrite (KP 18%bv ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)), Q18; exact G18|].
  rewrite (KP 24%bv ltac:(change (bv_unsigned (24%bv : bv 5)) with 24; unfold acallee_saved; lia)), Q24. exact G24. }
split; [rewrite (KP 22%bv ltac:(change (bv_unsigned (22%bv : bv 5)) with 22; unfold acallee_saved; lia)), Q22; reflexivity|].
split.
{ split.
  - apply (gx_rd_tr (aview SEGS (w_H W3) (ms_mem ms3))); [|exact Sra].
    intros j Hj. apply KB; lia.
  - intros j Hj. apply (gx_rd_tr (aview SEGS (w_H W3) (ms_mem ms3))); [|exact (Ssv j Hj)].
    intros jj Hjj. apply KB; lia. }
split.
{ apply (gx_rd_tr (aview SEGS (w_H W3) (ms_mem ms3))); [|exact HFLW].
  intros j Hj. rewrite Hfb in *. apply KB; [lia | apply SHfr; lia | lia]. }
split.
{ apply (garr8_frame SEGS _ _ _ _ HIN). intros a Ha. rewrite length_map in Ha.
  destruct (gx_input_blk cx ly3 S3 W3 (ms_mem ms3) md3 HB HAR3 Hsub a ltac:(unfold c_n; lia)) as (Ha0 & _ & _ & Hap & Hnf).
  pose proof (Hnf GB_CID fp ltac:(rewrite HFR; left; reflexivity)) as Hnf'. rewrite EF, Hfb in Hnf'.
  apply (mbyte_of_aview SEGS). apply KB; [lia | exact (SHapp a Hap) | lia]. }
split; [exact Hk|]. split; [exact Hacc | exact HPerm].
Qed.

(* ---- 0x80e14 .. 0x80e1c: free (r), the table the call allocated ---- *)
Theorem gx_seg_free : forall POST, gb_from B MT POST GI_XA -> gb_from B MT POST (GI_X B MT).
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & HBODY & Hk & Hacc & HBLK & Hrin & R20).
destruct HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & (G2 & G8 & G9 & G3 & G4 & G18 & G24) &
  (Sra & Ssv) & HSH & Hlen & HFLW & (L18 & L28 & L70 & L78 & L80) & HIN).
pose proof HB as (HPRE & _ & _ & Hpn & _ & _ & Hev & _ & _ & _ & _ & _ & _ & HMOK & HTR & HNEED).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & _).
destruct (gx_geo cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ HFR) as
  ((Hsp & Hal16 & Hsp1 & Hsp32) & (EF & EFL & Hfb & ESH) & (HF0 & HFc & HFia) & _ & HFRB & _).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & Hnev3 & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_B_ok (PAImg := PI)) as HBASE. pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
unfold GB_STK in Hsp.
destruct (gx_shadow_sep (gF cx fp) HF0 HFc HFia) as (SHapp & SHfr & SHc). rewrite <- ESH in SHapp, SHfr, SHc.
assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
unfold gblk1 in HBLK.
assert (Hsub : forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3))
  by (intros b Hb; rewrite HBLK; apply in_or_app; left; exact Hb).
(* r is not one of the caller's blocks: the blocks are disjoint and r is the last of them. *)
assert (Hnotin : ~ In (r, REG_SIZE) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hin. apply in_split in Hin as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (r, REG_SIZE) (r, REG_SIZE) l1 l2 [] HAR3
    ltac:(rewrite HBLK, El, <- app_assoc; reflexivity)) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size REG_SIZE) with 288 in D. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hrin) as (_ & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ GB_CID fp HAR3 Hrin Hfin) as DRF.
rewrite EF, Hfb in DRF. unfold zdisjoint in DRF. cbn [fst snd] in DRF. change (req_size REG_SIZE) with 288 in DRF.
rewrite (gx_mkst ms3 GP_X Hpc Hresv Hsvc Hrom Hfrg Hfcsr).
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr (ms_regs ms3) rr)
  by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E gx_ssA
  (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_X)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold gx_ssA. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS GX_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
pose proof (paj_run B LAWS) as RUN.
paj_run_tok RUN HS HJ SHOK GX_span; [apply awr_ok_nil |].
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms1 end.
(* The run wrote nothing. *)
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha.
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ms1)) |- _ =>
    cbn [ms_mem mkst] in HFx;
    apply (kept_of_frame E _ (w_H W3) _ _ (fun _ => False) HFx); [|exact Ha | intros []] end.
  intros b wlo whi x Hin _. unfold gx_ssA in Hin. cbn [ss_mem windows map In] in Hin. destruct Hin. }
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. rewrite (EE 2%nat 2%bv eq_refl) in Q2.
prreg HS (3%bv : bv 5) Q3. rewrite (EE 3%nat 3%bv eq_refl) in Q3.
prreg HS (4%bv : bv 5) Q4. rewrite (EE 4%nat 4%bv eq_refl) in Q4.
prreg HS (8%bv : bv 5) Q8. rewrite (EE 8%nat 8%bv eq_refl) in Q8.
prreg HS (9%bv : bv 5) Q9. rewrite (EE 9%nat 9%bv eq_refl) in Q9.
prreg HS (10%bv : bv 5) Q10. rewrite (EE 20%nat 20%bv eq_refl) in Q10.
prreg HS (18%bv : bv 5) Q18. rewrite (EE 18%nat 18%bv eq_refl) in Q18.
prreg HS (24%bv : bv 5) Q24. rewrite (EE 24%nat 24%bv eq_refl) in Q24.
assert (Usp : spZ (ms_regs ms1) = c_sp1 cx) by (unfold spZ; rewrite Q2, G2; unfold w64; apply unsigned_lit_small; lia).
pmkst HS. rewrite (pal_free B TL).
(* The chain the wrapper gets. *)
assert (H8 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
{ apply (gx_rd_tr (aview SEGS (w_H W3) (ms_mem ms3))); [|exact Sra]. intros j Hj. apply M1. lia. }
assert (H16 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ apply (gx_rd_tr (aview SEGS (w_H W3) (ms_mem ms3))); [intros j Hj; apply M1; lia|].
  pose proof (Ssv 0 ltac:(lia)) as S0. rewrite Z.mul_0_r, Z.sub_0_r in S0. exact S0. }
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx)).
{ apply (gx_achain cx ly3 _ (c_sp1 cx) HB Etop); [| exact H8 | exact H16 | lia].
  intros a Ha. rewrite (M1 a ltac:(lia)). apply F1; lia. }
eapply SRr_bind.
{ eapply (AFREE4 W3 (ms_regs ms1) (ms_mem ms1) GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k r REG_SIZE (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + GX_A)) (gch cx) HJ).
  - exact Hrin.
  - rewrite Q10. exact R20.
  - rewrite Usp. lia.
  - exact (gx_mod16 _ _ Hsp32 Hal16).
  - lia.
  - unfold GB_STK. assert (ASTACK = 16384) as Has by reflexivity. lia.
  - rewrite Q3, G3. exact Hgp.
  - rewrite Q4, G4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold GX_A; lia | reflexivity].
  - unfold GB_EV in Hev. lia.
  - apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) (gch cx) (ms_regs ms1) HCH).
    + rewrite Usp. lia.
    + unfold s0Z. rewrite Q8, G8. unfold w64. apply unsigned_lit_small. lia.
    + unfold raZ. rewrite Q1, unsigned_lit_small by (unfold GX_A; lia). unfold GX_A; lia.
  - apply HTR. right. split; [reflexivity|]. unfold raZ. rewrite Q1, unsigned_lit_small by (unfold GX_A; lia).
    unfold GB_FSITES, GX_A. cbn [In]. lia.
  - intros Hin. exfalso. exact (Hnotin Hin).
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MTL HMOK HMO);
      [apply (mo_free_nonneg MT MTL) | unfold GB_NEED in HNEED; lia]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & Hfrs2 & HK2 & MLE2).
destruct HK2 as (K1 & K2 & _ & K4 & _).
assert (KP : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr (ms_regs ms1) rr).
{ intros rr Hr. pose proof (HP2 (bv_unsigned rr) Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
(* What the call kept: the machine frame from s1 up, the side-stack frame, its shadow, the caller's input. *)
assert (Khi : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite (K1 a ltac:(lia) ltac:(lia)). apply M1. lia. }
assert (Kfr : forall a, gF cx fp <= a < gF cx fp + 512 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite (K4 GB_CID fp a Hfin); [apply M1; lia | | cbv beta; change (req_size REG_SIZE) with 288; lia].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, Hfb. lia. }
assert (Ksh : forall a, gSH cx fp <= a < gSH cx fp + 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha.
  assert (HSH0 : 0 <= gSH cx fp) by (rewrite ESH; unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (gF cx fp) 8); lia).
  rewrite (K4 GB_CID fp a Hfin); [apply M1; lia | |].
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, <- ESH, Hfb. change (512 / 8) with 64. lia.
  - cbv beta. change (req_size REG_SIZE) with 288. intros Hx.
    exact (SHapp a (in_app_addr _ _ a Hria Hx) Ha). }
assert (Kin : forall a, c_p cx <= a < c_p cx + c_n cx -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. pose proof HB as (_ & _ & _ & Hpn' & _).
  destruct Hpn' as [[Hn0 _] | [Hn Hin0]]; [lia|].
  assert (Hne : (c_p cx, c_n cx) <> (r, REG_SIZE)) by (intros Heq; rewrite Heq in Hin0; exact (Hnotin Hin0)).
  pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 (Hsub _ Hin0) Hrin Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. change (req_size REG_SIZE) with 288 in D.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
  destruct (gx_input_blk cx ly3 S3 W3 (ms_mem ms3) md3 HB HAR3 Hsub a Ha) as (Ha0 & _).
  replace a with (c_p cx + (a - c_p cx)) by lia.
  rewrite (K2 (c_p cx) (c_n cx) (a - c_p cx) (Hsub _ Hin0) ltac:(lia)); [apply M1; lia|].
  cbv beta. change (req_size REG_SIZE) with 288. lia. }
assert (HPerm2 : Permutation (ablocks B ly2 S2) (ablocks B (c_ly cx) (c_S cx))).
{ rewrite E2. apply (Permutation_app_inv_r [(r, REG_SIZE)]). rewrite <- HBLK, E1, <- app_assoc.
  apply Permutation_app_head. cbn [app]. apply Permutation_sym. apply Permutation_cons_append. }
apply (HNEXT cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + GX_A)) mem2 (seg_rom SEGS)) md2
  HB HJ2 (eq_trans Hfrs2 HFR) (mle_station MT (c_S cx) S3 S2 acc (mo_free MT) MTL HMO MLE2)).
unfold GI_XA. split; [|split; [lia | split; [unfold GB_NEED in *; lia | exact HPerm2]]].
unfold gb_body, gregs, gsaved, gshadow, gslots_fr, gslot.
cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{ split; [rewrite (KP 2%bv ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)), Q2; exact G2|].
  split; [rewrite (KP 8%bv ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)), Q8; exact G8|].
  split; [rewrite (KP 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)), Q9; exact G9|].
  split; [rewrite (KP 3%bv ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)), Q3; exact G3|].
  split; [rewrite (KP 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), Q4; exact G4|].
  split; [rewrite (KP 18%bv ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)), Q18; exact G18|].
  rewrite (KP 24%bv ltac:(change (bv_unsigned (24%bv : bv 5)) with 24; unfold acallee_saved; lia)), Q24. exact G24. }
split.
{ split.
  - apply (gx_rd_tr (aview SEGS (w_H W3) (ms_mem ms3))); [|exact Sra]. intros j Hj. apply Khi. lia.
  - intros j Hj. apply (gx_rd_tr (aview SEGS (w_H W3) (ms_mem ms3))); [|exact (Ssv j Hj)].
    intros jj Hjj. apply Khi. lia. }
split.
{ intros i Hi. rewrite Ksh; [exact (HSH i Hi) | rewrite Hlen in Hi; unfold GB_NSH in Hi; lia]. }
split; [exact Hlen|].
split.
{ apply (gx_rd_tr (aview SEGS (w_H W3) (ms_mem ms3))); [|exact HFLW].
  intros j Hj. rewrite Hfb in *. apply Kfr. lia. }
split.
{ repeat split;
    (apply (gx_rd_tr (aview SEGS (w_H W3) (ms_mem ms3))); [intros j Hj; apply Khi; lia | assumption]). }
{ apply (garr8_frame SEGS _ _ _ _ HIN). intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview SEGS). apply Kin. unfold c_n. lia. }
Qed.

(* ---- the phase: from the cut X, free (r), the frame given back, the return ---- *)
Theorem gb_exit : gb_from B MT (gb_post B MT) (GI_X B MT).
Proof. exact (gx_seg_free _ (gx_seg_shadow _ gx_seg_ret)). Qed.

End c.
End b.
End a.
