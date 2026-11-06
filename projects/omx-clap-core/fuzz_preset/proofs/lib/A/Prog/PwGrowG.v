(* fuzz_preset, program walks of grow (preset_file.c:42-64), the part that is NOT computed on a listing: the facts the
   walk needs about where the node v lies, what a fuzz_realloc call leaves of it, and how the walk's own stores leave
   the alloc.c ledger. GENERIC in the image (any {L : ptable asym} {PA : PAImg L}), in the allocator relation ARx with
   its laws, in the statics PST and in the sink head SK; image A's walk (lib/A/Prog/PwGrow.v) and image B's twin
   (image B's twin) both import it and write only their own run lemmas.
   the kit's text of grow is tgrow_specX (lib/A/PRH_FnReader.v, blob f1ae32e3b2cd at the kit's cut 7cdbb61b5fa0); its callee's
   text is tfuzz_realloc_specX (lib/A/PRH_FnAlloc.v, blob 4d8aeba047e5 at the cut), a STATED HYPOTHESIS until S1's walk
   lands. The harness-block shadow law is AR_laws_x field 15 (alx_hshadow, YCbqG blob 219748197d6b at the cut), at
   hl := cf_head.
   Numerals: 56, 40, 32, 24, 48, 8, 4 are LENGTH (struct pj's field offsets and widths, preset_file.c:25-33);
   16 and 4096 are LENGTH (the allocator's alignment and its lowest block); 6 is a WORD (PJ_OBJ, the type tag).
   No address, no image constant. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI00 YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK06 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC80xf YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoom PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the engine's laws at the harness head length (YCbqG's AR_laws_x takes hl; grow needs field 14 at cf_head) *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* the harness-block shadow law: AR_laws_x field 14 *)
Let HSH : ARx_hshadow_law segs B ARx cf_head := alx_hshadow segs B ARx LAWS.
#[local] Notation PST := (@prh_pst PI).
(* THE WORLD RELATION OF THE FREE / REALLOC MOVE (the move's shape note sec. 1): after a free or a realloc of a live
   block the hidden set may grow inside the fixed zone RZ_cf, so every journal / kept relation / post of grow's walk
   past its first realloc is at wle' segs RZ_cf. The walk lifts once at its top (the journal starts there), so these
   lemmas, used only by grow's walks, are restated in place at this R (the decided rule for a definition used only
   after a free / realloc). *)
#[local] Notation RW := (wle' segs RZ_cf).

(* ---- where the node lies ---- *)

(* prhReader_at's four cases at (v, 56), with the harness-block case resolved to its allocator block: a walk's engine
   needs the BLOCK, and prh_ledger turns a ledger entry into one. The fourth case (the caller's granted extension)
   and the third (a live fake frame) are the harness's: preset keeps its structs in class-0 / class-1 fake frames. *)
Definition grow_vloc (ly : alayout) (S : astate) (regs : bvmap 5 word) (e v : Z) : Prop :=
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= v /\ v + 56 <= b + req_size m) \/
  (exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
  (spZ regs <= v /\ v + 56 <= spZ regs + e).

(* the kit's prhReader_at gives grow_vloc: a ledger entry is a harness block of the allocator (prh_hblock), whose request
   size is at least its user size *)
Lemma grow_vloc_of_at : forall ly S Hp W mem Lam peak cnt fail ran most own regs e v,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> grow_vloc ly S regs e v.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own regs e v (_ & _ & HF & _) [(a & k & Hin & H1 & H2) | [H | [H | H]]].
- left. pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk & Hb & _). cbn [fst snd] in Hk, Hb.
  exists (a - cf_head), (k + cf_head). split; [exact Hb|].
  pose proof cf_head_nonneg as Hh.
  assert (Hq : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  split; lia.
- left. destruct H as (b & m & Hin & _ & H1 & H2). exists b, m.
  assert (Hq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  split; [exact Hin|]. split; lia.
- right; left. exact H.
- right; right. exact H.
Qed.

(* what the laws give about WHERE the node lies, in each case of grow_vloc: it is application memory (so apart from
   the shadow band, which is exactly [SHADOW_OFF, kHighMemBeg)), it is off the image, it is below 2 ^ 47, and it does
   not meet the walk's own frame [sp - 80, sp). A block and a frame are below alloc_ceiling (so below the frame only
   in the first disjunct); the granted extension is at or above sp. *)
Lemma grow_vbounds : forall ly S Hp W mem md STK FR regs e v,
  ARx ly S Hp W mem md -> astk_ok STK ly (spZ regs) -> 0 <= FR -> FR <= STK -> 0 <= e -> spZ regs + e <= ly_top ly ->
  grow_vloc ly S regs e v ->
  4096 <= v /\ v + 56 <= 2 ^ 47 /\ (v + 56 <= spZ regs - FR \/ spZ regs <= v) /\
  (forall a, v <= a < v + 56 -> ~ in_img segs a) /\
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
Proof.
intros ly S Hp W mem md STK FR regs e v HAR (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2) HFR0 HFR He Hetop HL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ L PA) as Hsl.
assert (HAPP : (4096 <= v /\ v + 56 <= YM05.alloc_ceiling /\ in_app v 56 /\
                 (forall a, v <= a < v + 56 -> ~ in_img segs a)) \/
               (spZ regs <= v /\ v + 56 <= spZ regs + e)).
{ destruct HL as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & H1 & H2) | H]].
  - destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & H4096 & Hc & Happ & _).
    left. split; [lia|]. split; [lia|]. split;
      [exact (in_app_sub b (req_size m) v 56 Happ H1 ltac:(lia) H2)|].
    intros a Ha. assert (Hr : b <= a < b + req_size m) by lia.
    exact (proj2 (alx_client_img segs B ARx LAWS ly S Hp W mem md a HAR
      (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Hr)))))).
  - destruct (alx_frames segs B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Happ & _).
    destruct (alx_sep segs B ARx LAWS ly S Hp W mem md HAR) as (_ & Hfr).
    pose proof (proj1 (Forall_forall _ _) Hfr (cid, pos) Hin) as (Hf4096 & Hfc). cbn [fst snd] in Hf4096, Hfc.
    left. split; [lia|]. split; [lia|]. split;
      [exact (in_app_sub (frame_addr ly cid pos) (fs_frame_bytes cid) v 56 Happ H1 ltac:(lia) H2)|].
    intros a Ha. assert (Hr : frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) by lia.
    exact (proj2 (alx_client_img segs B ARx LAWS ly S Hp W mem md a HAR
      (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Hr))))))).
  - right. exact H. }
destruct HAPP as [(H4096 & Hcl & Happ & Hoff) | (H1 & H2)].
- split; [exact H4096|]. split; [lia|]. split; [left; lia|]. split; [exact Hoff|].
  intros a Ha. pose proof (in_app_addr v 56 a Happ Ha) as (Hlo & [Hx | (Hx & _)]);
    unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *; lia.
- split; [lia|]. split; [lia|]. split; [right; lia|].
  split; [intros a Ha Hi; pose proof (Hsl a Hi); unfold kLowMemEnd in *; lia|].
  intros a Ha. unfold SHADOW_OFF. lia.
Qed.

(* an 8-byte image cell (the GOT word, the shadow-base cell) is apart from the node, because every byte of the node
   is off the image *)
Lemma range_apart_img : forall c v,
  (forall i, 0 <= i < 8 -> in_img segs (c + i)) ->
  (forall a, v <= a < v + 56 -> ~ in_img segs a) ->
  v + 56 <= c \/ c + 8 <= v.
Proof.
intros c v Hc Hv. destruct (Z_le_gt_dec (v + 56) c) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (c + 8) v) as [H2|H2]; [right; exact H2|]. exfalso.
assert (Hi : 0 <= Z.max v c - c < 8) by lia.
assert (Ha : v <= Z.max v c < v + 56) by lia.
apply (Hv _ Ha). replace (Z.max v c) with (c + (Z.max v c - c)) by lia. exact (Hc _ Hi).
Qed.

(* ---- the write permission of grow's windows ---- *)

(* grow writes its own frame (FR bytes: image A 80, image B 96 = pi_frame F_grow) and three fields of v (kids at
   v + 24, keys at v + 32, cap at v + 48: A 0x86a7c,
   0x86ac8, 0x86ad8). With the caller-frame runners (YC80xf.v, awr_ok_fr) each case of grow_vloc is permitted:
   a block in FP, a live frame in FP, or the walk's own window. *)
Lemma grow_awr_ok_fr : forall E rs STK FR e sp FP bl0 blc S ly v,
  0 <= FR -> FR <= STK -> 0 <= e ->
  (forall a, in_wrange E rs a -> (sp - FR <= a < sp) \/ (v + 24 <= a < v + 40) \/ (v + 48 <= a < v + 56)) ->
  (forall a, (v + 24 <= a < v + 40) \/ (v + 48 <= a < v + 56) -> inFP FP a) ->
  ((exists b m, In (b, m) blc /\ b <= v /\ v + 56 <= b + req_size m) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
   (sp <= v /\ v + 56 <= sp + e)) ->
  awr_ok_fr E rs (STK + e) (sp + e) FP bl0 blc S ly [].
Proof.
intros E rs STK FR e sp FP bl0 blc S ly v HFR0 HFR He Hw HF Hloc a Ha.
destruct (Hw a Ha) as [Hs | Hv]; [left; left; lia|].
destruct Hloc as [(b & m & Hb & Hb1 & Hb2) | [(cid & pos & Hc & Hc1 & Hc2) | (H1 & H2)]].
- left; right; left. split; [apply HF; exact Hv|]. exists b, m. split; [exact Hb | lia].
- right. split; [apply HF; exact Hv|]. exists cid, pos. split; [exact Hc|]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- left; left. lia.
Qed.

(* the footprint the kit's text gives grow holds its two written windows *)
Lemma grow_FP_v : forall v ty kids keys cap a,
  (v + 24 <= a < v + 40) \/ (v + 48 <= a < v + 56) ->
  inFP ([(v + 24, v + 40); (v + 48, v + 56)] ++
        ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap))) a.
Proof.
intros v ty kids keys cap a [Ha | Ha]; [exists (v + 24, v + 40) | exists (v + 48, v + 56)];
  (split; [cbn; tauto | cbn [fst snd]; lia]).
Qed.

(* ---- what a memory change leaves ---- *)

(* a value read through val_mem survives a change that leaves its bytes alone *)
Lemma val_mem_keep : forall (m m' : word -> option byte) a n w,
  val_mem segs m a n w ->
  (forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem segs m' a n w.
Proof. intros m m' a n w H Hk k Hlt. specialize (H k Hlt). unfold mbyte in *. rewrite (Hk k Hlt). exact H. Qed.

(* bytes outside every write window of an engine stretch keep their view *)
Lemma frame_aview : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' a Hfr Ha Hn. unfold aview, mbyte, mrestrict.
rewrite (Hfr (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

(* ---- the ledger across grow's own stores ---- *)

(* the bytes prh_ledger reads: the seven statics at their generated widths (#102's prh_glob: alloc.c's five, g_most,
   g_own_ran_out), and the head word of each harness block *)
Definition prh_cell (Lam : list (Z * Z)) (a : Z) : Prop :=
  (exists i, 0 <= i < Z.of_nat pi_gz_live /\ a = pi_g_live + i) \/
  (exists i, 0 <= i < Z.of_nat pi_gz_peak /\ a = pi_g_peak + i) \/
  (exists i, 0 <= i < Z.of_nat pi_gz_count /\ a = pi_g_count + i) \/
  (exists i, 0 <= i < Z.of_nat pi_gz_fail /\ a = pi_g_fail + i) \/
  (exists i, 0 <= i < Z.of_nat pi_gz_ran_out /\ a = pi_g_ran_out + i) \/
  (exists i, 0 <= i < Z.of_nat pi_gz_most /\ a = pi_g_most + i) \/
  (exists i, 0 <= i < Z.of_nat pi_gz_own_ran_out /\ a = pi_g_own_ran_out + i) \/
  (exists p k i, In (p, k) Lam /\ 0 <= i < 8 /\ a = p - cf_head + i).

Lemma prh_ledger_keep : forall ly S Hp (W : world segs) mem mem' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, prh_cell Lam a -> mrestrict (w_H W) mem' (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)) ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' Lam peak cnt fail ran most own
  ((V1 & V2 & V3 & V4 & V5 & (VM & RM) & (VO & RO) & R) & ND & F & P) Hc.
split; [|split; [exact ND | split; [|exact P]]].
- split; [apply (val_mem_keep _ _ _ _ _ V1); intros k Hk; apply Hc; left; exists (Z.of_nat k); split; [lia | reflexivity]|].
  split; [apply (val_mem_keep _ _ _ _ _ V2); intros k Hk; apply Hc; right; left; exists (Z.of_nat k); split; [lia | reflexivity]|].
  split; [apply (val_mem_keep _ _ _ _ _ V3); intros k Hk; apply Hc; right; right; left; exists (Z.of_nat k); split; [lia | reflexivity]|].
  split; [apply (val_mem_keep _ _ _ _ _ V4); intros k Hk; apply Hc; right; right; right; left; exists (Z.of_nat k); split; [lia | reflexivity]|].
  split; [apply (val_mem_keep _ _ _ _ _ V5); intros k Hk; apply Hc; right; right; right; right; left; exists (Z.of_nat k); split; [lia | reflexivity]|].
  split; [split; [|exact RM]; apply (val_mem_keep _ _ _ _ _ VM); intros k Hk; apply Hc; right; right; right; right; right; left;
    exists (Z.of_nat k); split; [lia | reflexivity]|].
  split; [split; [|exact RO]; apply (val_mem_keep _ _ _ _ _ VO); intros k Hk; apply Hc; right; right; right; right; right; right;
    left; exists (Z.of_nat k); split; [lia | reflexivity]|].
  exact R.
- apply Forall_forall. intros [a k] Hin. pose proof (proj1 (Forall_forall _ _) F (a, k) Hin) as (H1 & H2 & H3 & H4 & H5).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  apply (val_mem_keep _ _ _ _ _ H5). intros j Hj. apply Hc. right; right; right; right; right; right; right.
  exists a, k, (Z.of_nat j). split; [exact Hin|]. split; [lia | reflexivity].
Qed.

(* ---- a small list fact the block case needs (the statement of lib/A/AFkn.v:1051's pairwise_In_any) ---- *)
Lemma pairwise_In_any {X} : forall (R : X -> X -> Prop) (l : list X) x y,
  pairwise R l -> In x l -> In y l -> x = y \/ R x y \/ R y x.
Proof.
intros R l. induction l as [|z l IH]; intros x y P Hx Hy; [destruct Hx|]. cbn in P. destruct P as [F P].
destruct Hx as [<-|Hx], Hy as [<-|Hy];
  [left; reflexivity | right; left; exact (proj1 (Forall_forall _ _) F y Hy)
  | right; right; exact (proj1 (Forall_forall _ _) F x Hx) | exact (IH x y P Hx Hy)].
Qed.

(* ---- the node's shadow ---- *)

(* grow reads v's shadow at entry and re-reads it after each fuzz_realloc (A 0x86a74, 0x86ac0, 0x86acc). Three of
   prhReader_at's four cases give it from the laws at the state itself: a harness block's user range by the
   harness-block shadow law (its head is hidden, so YCbqG's alx_shadow says nothing about it), any other live
   allocator block by alx_shadow, the real stack by alx_zshadow_byte. The FAKE-FRAME case cannot come from a law -
   a frame's redzone shadow is poisoned, and which slots are live is the harness's business - so it is a premise
   HFR, which the caller meets at entry from the kit's own range_addressable premise and after a call by ajournal_x's
   frame clause (the frame and its shadow are kept outside the callee's FP). *)
Lemma grow_v_shadow : forall ly S Hp W mem md Lam peak cnt fail ran most own regs e v,
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 ->
  ly_stk_lo ly <= spZ regs -> spZ regs + e <= ly_stk_hi ly ->
  ((exists cid pos, In (cid, pos) (frames S) /\
      frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid) ->
   range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e v HAR HL HAt Hlo Hhi HFR.
destruct HAt as [(a & k & Hin & H1 & H2) | [(b & m & Hin & Hnot & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- (* a harness block: its user range, by the harness-block shadow law *)
  pose proof HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk & Hb & Hhp & _). cbn [fst snd] in Hk, Hb, Hhp.
  pose proof cf_head_nonneg as Hh.
  assert (Hq : 0 < req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); cbn; lia).
  destruct (HSH ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hb Hhp) as (HBS & _).
  replace (a - cf_head + cf_head) with a in HBS by lia.
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hb) as (_ & Hlo4096 & _).
  apply (block_shadow_range _ _ a (req_size (k + cf_head) - cf_head) v 56 HBS); lia.
- (* another live allocator block: no hidden head inside it, so alx_shadow gives its whole block shadow *)
  pose proof HL as (_ & _ & _ & HP).
  destruct (alx_shadow segs B ARx LAWS ly S Hp W mem md b m HAR Hin) as (HBS & _).
  { intros h Hhin Hr.
    (* h is the base of a harness block, whose allocator block is live; two live blocks are disjoint, so a hidden
       head inside (b, m) forces that block to BE (b, m), which this case excludes *)
    pose proof (Permutation_in _ HP Hhin) as Hmap. apply in_map_iff in Hmap as ((a0 & k0) & Heq & Hin0).
    cbn [fst] in Heq. pose proof HL as (_ & _ & HF & _).
    pose proof (proj1 (Forall_forall _ _) HF (a0, k0) Hin0) as (Hk0 & Hb0 & _). cbn [fst snd] in Hk0, Hb0.
    destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & _ & _ & _ & _ & Hpw).
    pose proof cf_head_nonneg as Hh.
    assert (Hq0 : 0 < req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); cbn; lia).
    destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md (a0 - cf_head) (k0 + cf_head) HAR Hb0) as (_ & _ & _ & _ & _ & _).
    destruct (pairwise_In_any _ _ (b, req_size m) (a0 - cf_head, req_size (k0 + cf_head)) Hpw
      ltac:(apply in_map_iff; exists (b, m); split; [reflexivity | exact Hin])
      ltac:(apply in_map_iff; exists (a0 - cf_head, k0 + cf_head); split; [reflexivity | exact Hb0]))
      as [Heqp | [Hdis | Hdis]].
    - injection Heqp as Hb1 Hb2.
      assert (Hm56 : 56 <= m) by (unfold req_size in H2; destruct (Z.eqb_spec m 0); lia).
      assert (Hk0m : k0 + cf_head = m)
        by (unfold req_size in Hb2; destruct (Z.eqb_spec m 0), (Z.eqb_spec (k0 + cf_head) 0); lia).
      apply Hnot. replace (b + cf_head) with a0 by lia. replace (m - cf_head) with k0 by lia. exact Hin0.
    - unfold zdisjoint in Hdis. cbn [fst snd] in Hdis. lia.
    - unfold zdisjoint in Hdis. cbn [fst snd] in Hdis. lia. }
  assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply (block_shadow_range _ _ b (req_size m) v 56 HBS); lia.
- (* a live fake frame: the caller's premise *)
  apply HFR. exists cid, pos. split; [exact Hin | split; [exact H1 | exact H2]].
- (* the real stack: the per-byte zero-shadow law *)
  intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. rewrite <- (alx_zshadow_byte segs B ARx LAWS ly S Hp W mem md x HAR ltac:(lia)).
  f_equal; lia.
Qed.

(* ---- the walk's bookkeeping, written for image B's walk (129171025fa,
   lib/B/Prog/PwGrowB.v:205-416) and moved here with the frame FR and the stack STK as parameters, so that both images
   use one copy. The statics are image bytes (HPST: at each instance by computation). ---- *)
Hypothesis HPST : forall a, Exists (in_zr a) PST -> in_img segs a.
(* the kept relation survives the model's materialization (the only model-bound clause is aos_step) *)
Lemma cj_kept_mat : forall STKf sp OR FPs lyc Sc (W : world segs) memc mdc ly2 S2 W2 mem2 md2 md3,
  cj_keptR (SK := SK) segs B PST RW STKf sp OR FPs lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  same_but_materialized md2 md3 ->
  cj_keptR (SK := SK) segs B PST RW STKf sp OR FPs lyc Sc W memc mdc ly2 S2 W2 mem2 md3.
Proof.
intros STKf sp OR FPs lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3 (H1 & H2 & H3 & H4 & H5) Hm.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
exact (aos_step_same_io _ _ _ _ H4 (same_io_materialized _ _ Hm)).
Qed.

(* THE RETURN: the walk at grow's `ret` (jalr x0, ra), its journal from entry and its kept relation from entry give
   the caller-window post; ra and the callee-saved registers are the entry's (symbolically back) *)
Lemma grow_ret : forall (PL : PAListing L) STK (W : world segs) E ss ms md e FP regs extra ly S Hp (W0 : world segs) mem md0 OR FPs
  ly2 S2 Hp2 k (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  0 <= STK ->
  st_ok_pi segs pa_val E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  plookup (@pl_tpi L PL) (ss_pc ss) = Some (PW RET_WORD_r) ->
  env_agree 32 (Ereg regs extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  sr_get (ss_regs ss) 1 = SOff 1 0 -> YK0s.ret_ok (getr regs 1) ->
  ajournal_xR (SK := SK) segs B PST ARx RW (STK + e) (spZ regs + e) FP ly S Hp W0 mem md0 []
    ly2 S2 Hp2 W (ms_mem ms) md k ->
  cj_keptR (SK := SK) segs B PST RW (STK) (spZ regs) OR FPs ly S W0 mem md0 ly2 S2 W (ms_mem ms) md ->
  (forall a, inFP OR a -> inFP FP a) ->
  (forall mat', Q ly2 S2 Hp2 W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat' md)) ->
  SRr' segs RZ_cf W (mkCfg ms md) (fpostW_xR (SK := SK) segs B PST ARx RW (STK) e FP regs ly S Hp W0 mem md0 Q).
Proof.
intros PL STK W E ss ms md e FP regs extra ly S Hp W0 mem md0 OR FPs ly2 S2 Hp2 k Q FS HS Hrv Hpl HA Hcs Hr1 Hra HJ HK HOR HQ.
(* the return makes no world step: the plain ret rule, lifted (YA0nH.SRr_SRr') *)
apply SRr_SRr'.
eapply ((@paj_ret_at fx rc L PL PA) W E ss ms md _ HS Hrv Hpl). intros mat'.
assert (HPC : v_jalr (getr (ms_regs ms) 1) 0 = getr regs 1).
{ pose proof (st_ok_pi_restrict_reg (w_H W) E ss ms 1%bv HS) as R1. rewrite Hr1 in R1.
  cbn [sv_denot] in R1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1.
  assert (Q1 : ew E 1 = getr regs 1).
  { pose proof (proj1 HA 1%nat ltac:(lia)) as H1. rewrite (ew_Ereg_nat regs extra 1 1%bv eq_refl) in H1. congruence. }
  rewrite R1, Q1. exact Hra. }
rewrite HPC.
apply (fpostW_x_of_keptR (SK := SK) segs B PST ARx RW (STK) e FP regs ly S Hp W0 mem md0 Q OR FPs
  ly2 S2 Hp2 W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat' md) k FS).
- exact (ajournal_x_materializeR (SK := SK) segs B PST ARx LAWS pa_segs_low RW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ).
- exact (cj_kept_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK (same_but_materialized_wvb_any md mat')).
- exact HOR.
- exact (aregs_preserved_of_st_ok segs (w_H W) E (abs_ss pa_val ss) ms regs extra HS HA Hcs).
- exact (HQ mat').
Qed.

(* ---- the walk's bookkeeping across engine stretches ---- *)

(* grow's write windows: its FR-byte frame below sp (image A 80, image B 96), and v's kids / keys and cap fields *)
Definition grow_wr (FR sp v a : Z) : Prop :=
  (sp - FR <= a < sp) \/ (v + 24 <= a < v + 40) \/ (v + 48 <= a < v + 56).
(* the cells of v grow writes, all in the kit's footprint *)
Definition grow_OR (v : Z) : list (Z * Z) := [(v + 24, v + 40); (v + 48, v + 56)].

(* the environment of every symbolic state of the walk agrees with the entry one below A_LIM *)
Lemma agree_ext : forall E0 E K ws, env_agree A_LIM E0 E -> (A_LIM <= K)%nat -> env_agree A_LIM E0 (extK E K ws).
Proof.
intros E0 E K ws [H1 H2] HK. destruct (env_agree_extK E K ws) as [G1 G2]. split.
- intros n Hn. rewrite (G1 n ltac:(lia)). exact (H1 n Hn).
- rewrite G2. exact H2.
Qed.
Lemma agree_Ereg : forall regs extra E', env_agree A_LIM (Eimg (PI := PA) (Ereg regs extra)) E' ->
  env_agree 32 (Ereg regs extra) E'.
Proof.
intros regs extra E' [H1 H2]. split.
- intros n Hn. rewrite (H1 n ltac:(unfold A_LIM; lia)). apply Eimg_low. unfold A_TEXT; lia.
- rewrite H2. reflexivity.
Qed.
Lemma U_agree : forall E0 E n z, env_agree A_LIM E0 E -> (n < A_LIM)%nat -> bv_unsigned (ew E0 n) = z ->
  bv_unsigned (ew E n) = z.
Proof. intros E0 E n z [H1 _] Hn Hz. rewrite (H1 n Hn). exact Hz. Qed.

(* one engine stretch at the current allocator state, writing only the walker's window and OR, extends the kept
   relation from entry (cj_kept_exec, then cj_kept_trans) *)
Lemma cj_kept_step : forall STKf sp OR FPs ly S Hp0 (W0 : world segs) mem md lyc Sc Hpc W memc mdc memc' mdc'
  (Wr : Z -> Prop),
  cj_keptR (SK := SK) segs B PST RW STKf sp OR FPs ly S W0 mem md lyc Sc W memc mdc ->
  ARx ly S Hp0 W0 mem md -> ARx lyc Sc Hpc W memc mdc ->
  YM05.alloc_ceiling <= ly_stk_lo lyc -> ly_stk_lo lyc <= sp - STKf -> sp <= ly_stk_hi lyc ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) memc' x = mrestrict (w_H W) memc x) ->
  (forall a, Wr a -> (sp - STKf <= a < sp) \/ inFP OR a) ->
  same_but_materialized mdc mdc' ->
  cj_keptR (SK := SK) segs B PST RW STKf sp OR FPs ly S W0 mem md lyc Sc W memc' mdc'.
Proof.
intros STKf sp OR FPs ly S Hp0 W0 mem md lyc Sc Hpc W memc mdc memc' mdc' Wr HK HAR0 HARc Hcl Hlo Hhi Hfr HW Hs.
apply (cj_kept_transR (SK := SK) segs B PST ARx LAWS RW (wle'_trans segs RZ_cf) STKf sp STKf sp OR FPs [] FPs ly S Hp0 W0 mem md
  lyc Sc Hpc W memc mdc lyc Sc W memc' mdc' HK); [| exact HAR0 | exact HARc | lia | lia | intros a Ha; left; exact Ha |].
- apply (cj_kept_execR (SK := SK) segs B PST ARx LAWS pa_segs_low RW (wle'_refl segs RZ_cf) STKf sp OR [] lyc Sc Hpc W memc mdc memc' mdc' Wr
    HARc Hcl Hlo Hhi Hfr); [|exact Hs].
  intros a Ha. destruct (HW a Ha) as [H | H]; [left; exact H | right; left; exact H].
- intros a (r & Hr & _). destruct Hr.
Qed.

(* a stretch's frame, through the window characterization of its symbolic memory *)
Lemma frame_grow : forall FR E rs (W : world segs) m m' sp v,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, in_wrange E rs a -> grow_wr FR sp v a) ->
  forall x : word, ~ grow_wr FR sp v (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x.
Proof. intros FR E rs W m m' sp v Hfr Hw x Hx. apply Hfr. intros Hin. exact (Hx (Hw _ Hin)). Qed.

(* ONE ENGINE STRETCH of the walk at the current allocator state: the kept relation from entry, the frame of grow's
   windows since the base memory memb (the memory after the last call), and the growth since memb *)
Lemma grow_stretch : forall STK FR E rs (W : world segs) memb memc mdc memc' mdc' sp v FP ly S Hp0 (W0 : world segs) mem md
  lyc Sc Hpc,
  0 <= FR -> FR <= STK ->
  cj_keptR (SK := SK) segs B PST RW STK sp (grow_OR v) FP ly S W0 mem md lyc Sc W memc mdc ->
  (forall x : word, ~ grow_wr FR sp v (bv_unsigned x) -> mrestrict (w_H W) memc x = mrestrict (w_H W) memb x) ->
  mem_grows (mrestrict (w_H W) memb) (mrestrict (w_H W) memc) ->
  ARx ly S Hp0 W0 mem md -> ARx lyc Sc Hpc W memc mdc ->
  YM05.alloc_ceiling <= ly_stk_lo lyc -> ly_stk_lo lyc + STK <= sp -> sp <= ly_stk_hi lyc ->
  frame_of E rs (mrestrict (w_H W) memc) (mrestrict (w_H W) memc') ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc') ->
  (forall a, in_wrange E rs a -> grow_wr FR sp v a) ->
  same_but_materialized mdc mdc' ->
  cj_keptR (SK := SK) segs B PST RW (STK) sp (grow_OR v) FP ly S W0 mem md lyc Sc W memc' mdc' /\
  (forall x : word, ~ grow_wr FR sp v (bv_unsigned x) -> mrestrict (w_H W) memc' x = mrestrict (w_H W) memb x) /\
  mem_grows (mrestrict (w_H W) memb) (mrestrict (w_H W) memc').
Proof.
intros STK FR E rs W memb memc mdc memc' mdc' sp v FP ly S Hp0 W0 mem md lyc Sc Hpc HFR0 FS HK HFR HGR HAR0 HARc Hcl Hlo Hhi Hfr Hg Hw Hs.
split; [|split].
- apply (cj_kept_step (STK) sp (grow_OR v) FP ly S Hp0 W0 mem md lyc Sc Hpc W memc mdc memc' mdc'
    (in_wrange E rs) HK HAR0 HARc Hcl ltac:(lia) Hhi Hfr); [|exact Hs].
  intros a Ha. destruct (Hw a Ha) as [H | [H | H]]; [left; lia | right | right].
  + exists (v + 24, v + 40). split; [cbn; tauto | cbn [fst snd]; lia].
  + exists (v + 48, v + 56). split; [cbn; tauto | cbn [fst snd]; lia].
- intros x Hx. rewrite <- (HFR x Hx). exact (frame_grow FR E rs W memc memc' sp v Hfr Hw x Hx).
- exact (mem_grows_trans _ _ _ HGR Hg).
Qed.

(* the node's header after stretches that wrote only grow's windows: the fields outside the windows (type, num, str,
   n) are the base memory's, the three written fields are given, and every byte stays writable *)
Lemma grow_hdr_keep : forall FR (H : word -> bool) memb mem2 sp v ty num str kids keys n cap kids2 keys2 cap2,
  pj_hdrR segs (mrestrict H memb) v ty num str kids keys n cap ->
  (forall x : word, ~ grow_wr FR sp v (bv_unsigned x) -> mrestrict H mem2 x = mrestrict H memb x) ->
  mem_grows (mrestrict H memb) (mrestrict H mem2) ->
  (v + 56 <= sp - FR \/ sp <= v) -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  rd_u64 segs (mrestrict H mem2) (v + 24) kids2 -> rd_u64 segs (mrestrict H mem2) (v + 32) keys2 ->
  rd_u64 segs (mrestrict H mem2) (v + 48) cap2 ->
  pj_hdrR segs (mrestrict H mem2) v ty num str kids2 keys2 n cap2.
Proof.
intros FR H memb mem2 sp v ty num str kids keys n cap kids2 keys2 cap2
  ((Hal & HRW) & (Hty & Vty) & (Hnum & Vnum) & (Hstr & Vstr) & _ & _ & (Hn & Vn) & _) HFR HGR Hvs Hv0 Hv64 Rk Ry Rc.
assert (KEEP : forall a (k : nat) w, val_mem segs (mrestrict H memb) a k w -> v <= a ->
  (a + Z.of_nat k <= v + 24 \/ (v + 40 <= a /\ a + Z.of_nat k <= v + 48)) ->
  val_mem segs (mrestrict H mem2) a k w).
{ intros a k w Hv Ha1 Ha2. eapply val_mem_keep; [exact Hv|]. intros j Hj. apply HFR.
  rewrite unsigned_lit_small by lia. unfold grow_wr in *. lia. }
split; [split; [exact Hal | intros x Hx; exact (writable_at_grows segs _ _ _ HGR (HRW x Hx))]|].
split; [split; [exact Hty | apply KEEP; [exact Vty | lia | cbn; lia]]|].
split; [split; [exact Hnum | apply KEEP; [exact Vnum | lia | cbn; lia]]|].
split; [split; [exact Hstr | apply KEEP; [exact Vstr | lia | cbn; lia]]|].
split; [exact Rk|]. split; [exact Ry|].
split; [split; [exact Hn | apply KEEP; [exact Vn | lia | cbn; lia]] | exact Rc].
Qed.

(* the cells the alloc.c ledger reads are outside grow's windows: the statics are image bytes (HPST), and a harness
   block's head word starts in its own allocator block, apart from the node's written fields wherever the node lies
   (a harness block - its own, whose head ends before the node's fields, or another -, another allocator block, a
   live fake frame, or the caller's extension) and below the frame *)
Lemma grow_cell_apart : forall FR ly S Hp (W : world segs) mem md Lam peak cnt fail ran most own regs e v a,
  0 <= FR <= 120 ->
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling + 128 <= spZ regs ->
  (forall x, v <= x < v + 56 -> ~ in_img segs x) ->
  prh_cell Lam a -> 0 <= a < 2 ^ 64 /\ ~ grow_wr FR (spZ regs) v a.
Proof.
intros FR ly S Hp W mem md Lam peak cnt fail ran most own regs e v a HFR HAR HL HAt Hsp Hoff Hc.
pose proof HL as (_ & HND & HF & _).
pose proof cf_head_nonneg as Hh0.
pose proof (@pa_segs_low _ L PA) as Hsl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hc as [(i & Hi & ->) | [(i & Hi & ->) | [(i & Hi & ->) | [(i & Hi & ->) | [(i & Hi & ->) |
  [(i & Hi & ->) | [(i & Hi & ->) | (p & k & i & Hin & Hi & ->)]]]]]]].
1-7: match goal with |- _ /\ ~ grow_wr _ _ _ ?x =>
       assert (Him : in_img segs x) by
         (apply HPST; unfold prh_pst;
          repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]));
       pose proof (Hsl _ Him) as Hlow; split; [unfold kLowMemEnd in *; lia|]; unfold grow_wr;
       intros [Hw | Hw]; [unfold kLowMemEnd in *; lia |];
       assert (Hxv : v <= x < v + 56) by lia; exact (Hoff x Hxv Him) end.
pose proof (proj1 (Forall_forall _ _) HF (p, k) Hin) as (Hk & Hb & _ & _ & _). cbn [fst snd] in Hk, Hb.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4096 & Hbc & _ & _ & _).
assert (Hq : k + cf_head <= req_size (k + cf_head) /\ 1 <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
split; [lia|]. unfold grow_wr. intros [Hw | Hw]; [lia|].
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & Hnot & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- destruct (Z.eq_dec a' p) as [-> | Hne]; [lia|].
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  assert (Hneq : (a' - cf_head, k' + cf_head) <> (p - cf_head, k + cf_head))
    by (intros Heq; injection Heq; intros; apply Hne; lia).
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hb' Hb Hneq) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia.
- assert (Hneq : (b, m) <> (p - cf_head, k + cf_head)).
  { intros Heq. injection Heq as E1 E2. apply Hnot. replace (b + cf_head) with p by lia.
    replace (m - cf_head) with k by lia. exact Hin. }
  assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hinb Hb Hneq) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia.
- pose proof (sep_block_frame_x segs B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hb Hinf) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia.
- lia.
Qed.


(* two ledger entries at one user address have one size (the ledger's addresses are distinct) *)
Lemma nodup_fst_eq : forall (l : list (Z * Z)) a b c, NoDup (map fst l) -> In (a, b) l -> In (a, c) l -> b = c.
Proof.
induction l as [|[x y] l IH]; intros a b c HN H1 H2; [destruct H1|].
cbn [map] in HN. inversion HN as [|? ? Hnin HN']; subst.
destruct H1 as [Hq | H1], H2 as [Hq' | H2].
- injection Hq as <- <-. injection Hq' as <-. reflexivity.
- injection Hq as <- <-. exfalso. apply Hnin.
  first [apply (proj2 (list_elem_of_In _ _)) | apply (proj2 (elem_of_list_In _ _))].
  apply in_map_iff. exists (x, c). split; [reflexivity | exact H2].
- injection Hq' as <- <-. exfalso. apply Hnin.
  first [apply (proj2 (list_elem_of_In _ _)) | apply (proj2 (elem_of_list_In _ _))].
  apply in_map_iff. exists (x, b). split; [reflexivity | exact H1].
- exact (IH a b c HN' H1 H2).
Qed.

(* the slot blocks the kit's footprint names (the kids and keys allocator blocks, heads included) are apart from grow's
   windows: below the frame (they are allocator blocks), and apart from the node's written fields wherever the node
   lies - in a harness block it lies in the user range: in the slot's own block pj_apartR excludes that, any other
   harness block is another allocator block; another allocator block, a live fake frame or the caller's extension are
   disjoint from every allocator block *)
Lemma grow_slot_apart : forall FR ly S Hp (W : world segs) mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap lo hi x,
  0 <= FR <= 120 -> 0 <= cap ->
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling + 128 <= spZ regs ->
  pj_slots_atR (prh_lin Lam) ty kids keys n cap -> pj_apartR (kids_blkR kids cap ++ keys_blkR ty keys cap) v ->
  In (lo, hi) (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap))) -> lo <= x < hi ->
  0 <= x < 2 ^ 64 /\ ~ grow_wr FR (spZ regs) v x.
Proof.
intros FR ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap lo hi x HFR Hc0 HAR HL HAt Hsp HSL HAP Hin Hx.
pose proof HL as (_ & HND & HF & _).
pose proof cf_head_nonneg as Hh0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold ablocks_fp, prhReader_ab in Hin. rewrite map_map in Hin. apply in_map_iff in Hin as ((u & k) & Heq & HinD).
cbn [fst snd] in Heq. injection Heq as Elo Ehi.
assert (HLu : In (u, k) Lam).
{ destruct HSL as (_ & _ & _ & HSL4). unfold kids_blkR, keys_blkR in HinD.
  destruct (Z.eqb_spec cap 0) as [H0|H0]; cbn [orb] in HinD; [destruct HinD|].
  assert (Hcp : 0 < cap) by lia. destruct (HSL4 Hcp) as (Hk1 & Hk2). unfold prh_lin in Hk1, Hk2.
  destruct (Z.eqb_spec ty 6) as [H6|H6]; cbn [negb app] in HinD.
  - destruct HinD as [Hq | [Hq | []]]; injection Hq as <- <-; [exact Hk1 | exact (Hk2 H6)].
  - destruct HinD as [Hq | []]; injection Hq as <- <-; exact Hk1. }
pose proof (proj1 (Forall_forall _ _) HF (u, k) HLu) as (Hk & Hb & _ & _ & _). cbn [fst snd] in Hk, Hb.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4096 & Hbc & _ & _ & _).
assert (Hq : k + cf_head <= req_size (k + cf_head) /\ 1 <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
split; [lia|]. unfold grow_wr. intros [Hw | Hw]; [lia|].
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & Hnot & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- destruct (Z.eq_dec a' u) as [-> | Hne].
  + assert (Ekk : k' = k) by exact (nodup_fst_eq Lam u k' k HND Hin' HLu). subst k'.
    assert (Hhold : pj_holdsR (u, k) v) by (unfold pj_holdsR; cbn [fst snd]; lia).
    assert (Hvv : v <= v < v + 56) by lia.
    exact (HAP (u, k) v HinD Hhold Hvv).
  + pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
    assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
    assert (Hneq : (a' - cf_head, k' + cf_head) <> (u - cf_head, k + cf_head))
      by (intros Heq; injection Heq; intros; apply Hne; lia).
    pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hb' Hb Hneq) as Hd.
    unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia.
- assert (Hneq : (b, m) <> (u - cf_head, k + cf_head)).
  { intros Heq. injection Heq as E1 E2. apply Hnot. replace (b + cf_head) with u by lia.
    replace (m - cf_head) with k by lia. exact HLu. }
  assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hinb Hb Hneq) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia.
- pose proof (sep_block_frame_x segs B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hb Hinf) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia.
- lia.
Qed.


(* grow keeps the node's cap field address in s0 across its calls (A 0x869f4 `mv s1, a0`, 0x86a0c
   `addi s0, s1, 48`), so the callee's
   fpre needs an unwinding chain at v + 48. In a harness block, in another live block and in a live fake frame that
   address is below alloc_ceiling, where a chain is empty (achain_low). In the caller's granted extension it is a
   real stack address, and the chain there is NOT derivable: the word the unwinder would read at (v + 48) - 16 is
   the node's keys field, which the kit's pj_slots_atR leaves free when ty <> 6, so bad_next cannot be decided. The kit gives
   exactly this premise for parse_string (PRH_FnReader.v:538 at the cut) and for grow (tgrow_specX, :825 at the cut);
   this lemma takes it as HEXT. *)
Lemma grow_s0_chain : forall ly S Hp (W : world segs) mem md Lam peak cnt fail ran most own regs e v sp',
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 ->
  (spZ regs <= v -> exists ch, achain ly (aview segs (w_H W) mem) sp' (v + 48) ch) ->
  exists ch, achain ly (aview segs (w_H W) mem) sp' (v + 48) ch.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e v sp' HAR HL HAt HEXT.
pose proof cf_head_nonneg as Hh0.
destruct (Z_lt_ge_dec (v + 48) YM05.alloc_ceiling) as [Hlow | Hhigh].
{ exists []. apply achain_low. exact Hlow. }
apply HEXT.
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & _ & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | H]]].
- pose proof HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & _ & Hbc & _).
  assert (Hq : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia). lia.
- destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hinb) as (_ & _ & Hbc & _).
  assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
- destruct (alx_sep _ _ _ LAWS _ _ _ _ _ _ HAR) as (_ & Hfr).
  pose proof (proj1 (Forall_forall _ _) Hfr (cid, pos) Hinf) as (_ & Hfc). cbn [fst snd] in Hfc. lia.
- lia.
Qed.


(* a chain survives a memory change that leaves the words the unwinder reads alone. The records of a chain at bp are
   at bp and above (fpchain's fp = bp, and each next frame is strictly higher), so agreement from bp - 16 up is
   enough; that is what grow's own stores leave, because they are below the node (its frame) or inside it. *)
Lemma achain_kept_hi : forall ly rd rd' sp v ch,
  achain ly rd sp v ch -> ly_top ly <= 2 ^ 64 ->
  (forall a, v - 16 <= a -> a < ly_top ly -> rd' a = rd a) ->
  achain ly rd' sp v ch.
Proof.
intros ly rd rd' sp v ch [H | (H1 & H2 & H3 & H4 & H5)] Htop Hag; [left; exact H|].
right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
eapply fpchain_ext; [| lia | exact H4]. intros a Ha1 Ha2. apply rdword_ext. intros k Hk. apply Hag; lia.
Qed.


(* two memories that hold the same 8-byte value at a give the same view on those bytes: val_mem fixes every byte *)
Lemma aview_of_val_mem_eq : forall (H : word -> bool) m m' a w,
  val_mem segs (mrestrict H m) a 8 w -> val_mem segs (mrestrict H m') a 8 w ->
  forall x, a <= x < a + 8 -> aview segs H m' x = aview segs H m x.
Proof.
intros H m m' a w Hm Hm' x Hx.
assert (Hk : (Z.to_nat (x - a) < 8)%nat) by lia.
pose proof (Hm _ Hk) as E1. pose proof (Hm' _ Hk) as E2.
replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E1, E2 by lia.
unfold aview. rewrite E1, E2. reflexivity.
Qed.

(* ---- what a fuzz_realloc call leaves of the node (shared by both images' walks) ---- *)

(* grow's slot blocks (the kids / keys arrays in their allocator form, grow's FP beyond the node's fields) lie apart
   from ALL of the node's 56 bytes: grow_slot_apart's case split, with the whole [v, v + 56) in place of grow_wr *)
Lemma grow_slot_v : forall ly S Hp (W : world segs) mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap lo hi x,
  0 <= cap ->
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling + 128 <= spZ regs ->
  pj_slots_atR (prh_lin Lam) ty kids keys n cap -> pj_apartR (kids_blkR kids cap ++ keys_blkR ty keys cap) v ->
  In (lo, hi) (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap))) -> lo <= x < hi ->
  ~ (v <= x < v + 56).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap lo hi x Hc0 HAR HL HAt Hsp HSL HAP Hin Hx Hw.
pose proof HL as (_ & HND & HF & _).
pose proof cf_head_nonneg as Hh0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold ablocks_fp, prhReader_ab in Hin. rewrite map_map in Hin. apply in_map_iff in Hin as ((u & k) & Heq & HinD).
cbn [fst snd] in Heq. injection Heq as Elo Ehi.
assert (HLu : In (u, k) Lam).
{ destruct HSL as (_ & _ & _ & HSL4). unfold kids_blkR, keys_blkR in HinD.
  destruct (Z.eqb_spec cap 0) as [H0|H0]; cbn [orb] in HinD; [destruct HinD|].
  assert (Hcp : 0 < cap) by lia. destruct (HSL4 Hcp) as (Hk1 & Hk2). unfold prh_lin in Hk1, Hk2.
  destruct (Z.eqb_spec ty 6) as [H6|H6]; cbn [negb app] in HinD.
  - destruct HinD as [Hq | [Hq | []]]; injection Hq as <- <-; [exact Hk1 | exact (Hk2 H6)].
  - destruct HinD as [Hq | []]; injection Hq as <- <-; exact Hk1. }
pose proof (proj1 (Forall_forall _ _) HF (u, k) HLu) as (Hk & Hb & _ & _ & _). cbn [fst snd] in Hk, Hb.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4096 & Hbc & _ & _ & _).
assert (Hq : k + cf_head <= req_size (k + cf_head) /\ 1 <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & Hnot & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- destruct (Z.eq_dec a' u) as [-> | Hne].
  + assert (Ekk : k' = k) by exact (nodup_fst_eq Lam u k' k HND Hin' HLu). subst k'.
    assert (Hhold : pj_holdsR (u, k) v) by (unfold pj_holdsR; cbn [fst snd]; lia).
    assert (Hvv : v <= v < v + 56) by lia.
    exact (HAP (u, k) v HinD Hhold Hvv).
  + pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
    assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
    assert (Hneq : (a' - cf_head, k' + cf_head) <> (u - cf_head, k + cf_head))
      by (intros Heq; injection Heq; intros; apply Hne; lia).
    pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hb' Hb Hneq) as Hd.
    unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia.
- assert (Hneq : (b, m) <> (u - cf_head, k + cf_head)).
  { intros Heq. injection Heq as E1 E2. apply Hnot. replace (b + cf_head) with u by lia.
    replace (m - cf_head) with k by lia. exact HLu. }
  assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hinb Hb Hneq) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia.
- pose proof (sep_block_frame_x segs B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hb Hinf) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia.
- lia.
Qed.

(* THE NODE ACROSS A fuzz_realloc CALL: the callee's journal (from the call state ly S Hp W memc mdc, its footprint
   FP1 among grow's slot blocks, its window below grow's sp) keeps every byte of v and leaves it present. The four
   cases of prhReader_at: a block holding v is still live after the call (else the journal's gone-clause would put
   v's bytes in FP1) and its clause keeps them; a fake frame by the frame clause; the caller's granted extension by the
   stack clause. Presence moves with the bytes (apresent_transfer: v is off the image), from the call state's laws or,
   for the extension, from the caller's window (Hpc). *)
Lemma grow_v_kept : forall ly S Hp (W : world segs) memc mdc Lam peak cnt fail ran most own regs e v ty kids keys n cap
  STK1 sp1 FP1 ly2 S2 Hp2 (W2 : world segs) mem2 md2 k1,
  0 <= cap ->
  ARx ly S Hp W memc mdc -> prh_ledger B ly S Hp W memc Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling + 128 <= spZ regs -> 4096 <= v -> v + 56 <= 2 ^ 64 ->
  (forall a, v <= a < v + 56 -> ~ in_img segs a) ->
  (forall a, spZ regs <= a < spZ regs + e -> apresent (w_H W) memc a) ->
  pj_slots_atR (prh_lin Lam) ty kids keys n cap -> pj_apartR (kids_blkR kids cap ++ keys_blkR ty keys cap) v ->
  ajournal_xR (SK := SK) segs B PST ARx RW STK1 sp1 FP1 ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  sp1 <= spZ regs ->
  (forall r, In r FP1 -> In r (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))) ->
  forall a, v <= a < v + 56 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a /\ apresent (w_H W2) mem2 a.
Proof.
intros ly S Hp W memc mdc Lam peak cnt fail ran most own regs e v ty kids keys n cap STK1 sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  Hc0 HAR HL HAt Hsp Hv0 Hv64 Hoff Hpc HSL HAP HJ Hsp1 HFP1 a Ha.
pose proof (ajxR_hi HJ) as G1. pose proof (ajxR_blk HJ) as G2. pose proof (ajxR_frm HJ) as G4.
pose proof (ajxR_gone HJ) as Hgone.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
assert (HnF : ~ inFP FP1 a).
{ intros ((lo & hi) & Hr & Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
  exact (grow_slot_v ly S Hp W memc mdc Lam peak cnt fail ran most own regs e v ty kids keys n cap lo hi a
    Hc0 HAR HL HAt Hsp HSL HAP (HFP1 _ Hr) ltac:(lia) Ha). }
assert (HTR : aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a -> apresent (w_H W) memc a ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a /\ apresent (w_H W2) mem2 a).
{ intros Hv Hpm. split; [exact Hv|]. eapply apresent_transfer; [lia | exact (Hoff a Ha) | exact Hv | exact Hpm]. }
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
assert (HBLK : forall p m, In (p, m) (ablocks B ly S) -> p <= v -> v + 56 <= p + req_size m ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a /\ apresent (w_H W2) mem2 a).
{ intros p m Hin Hpv1 Hpv2.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpr & _).
  apply HTR; [| exact (proj1 (Hpr a ltac:(lia)))].
  destruct (in_dec Hdec (p, m) (ablocks B ly2 S2)) as [Hin2 | Hout].
  - replace a with (p + (a - p)) by lia.
    apply (G2 p m (a - p) Hin Hin2); [lia |]. replace (p + (a - p)) with a by lia. exact HnF.
  - exfalso. apply HnF. replace a with (p + (a - p)) by lia. exact (Hgone p m (a - p) Hin Hout ltac:(lia)). }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & _ & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- pose proof HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  apply (HBLK _ _ Hb'); lia.
- assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply (HBLK _ _ Hinb); lia.
- destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ cid pos HAR Hinf) as (_ & _ & Hfp & _).
  apply HTR; [| exact (proj1 (Hfp a ltac:(lia)))].
  apply (G4 cid pos a Hinf); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnF].
- apply HTR; [apply G1; lia | apply Hpc; lia].
Qed.

(* WHERE THE NODE IS AFTER THE CALL: grow_vloc at the callee's post state. A block holding v is still live (the
   journal's gone-clause would otherwise put v's bytes in the callee's FP, which the slot blocks are apart from);
   a fake frame survives (frames S2 = [] ++ frames S, and layout_le keeps ly_F, hence frame_addr); the caller's
   granted extension is unchanged. The run lemmas after the call need exactly this. *)
Lemma grow_vloc2 : forall ly S Hp (W : world segs) memc mdc Lam peak cnt fail ran most own regs e v ty kids keys n cap
  STK1 sp1 FP1 ly2 S2 Hp2 (W2 : world segs) mem2 md2 k1,
  0 <= cap ->
  ARx ly S Hp W memc mdc -> prh_ledger B ly S Hp W memc Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling + 128 <= spZ regs ->
  pj_slots_atR (prh_lin Lam) ty kids keys n cap -> pj_apartR (kids_blkR kids cap ++ keys_blkR ty keys cap) v ->
  ajournal_xR (SK := SK) segs B PST ARx RW STK1 sp1 FP1 ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall r, In r FP1 -> In r (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))) ->
  grow_vloc ly2 S2 regs e v.
Proof.
intros ly S Hp W memc mdc Lam peak cnt fail ran most own regs e v ty kids keys n cap STK1 sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  Hc0 HAR HL HAt Hsp HSL HAP HJ HFP1.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_gone HJ) as Hgone.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
assert (HnFv : forall x, v <= x < v + 56 -> ~ inFP FP1 x).
{ intros x Hx ((lo & hi) & Hr & Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
  exact (grow_slot_v ly S Hp W memc mdc Lam peak cnt fail ran most own regs e v ty kids keys n cap lo hi x
    Hc0 HAR HL HAt Hsp HSL HAP (HFP1 _ Hr) ltac:(lia) Hx). }
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
assert (HBLK2 : forall p m, In (p, m) (ablocks B ly S) -> p <= v -> v + 56 <= p + req_size m ->
  grow_vloc ly2 S2 regs e v).
{ intros p m Hin Hpv1 Hpv2.
  destruct (in_dec Hdec (p, m) (ablocks B ly2 S2)) as [Hin2 | Hout].
  - left. exists p, m. split; [exact Hin2 | lia].
  - exfalso. apply (HnFv v ltac:(lia)). replace v with (p + (v - p)) by lia.
    exact (Hgone p m (v - p) Hin Hout ltac:(lia)). }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & _ & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- pose proof HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  apply (HBLK2 _ _ Hb'); lia.
- assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply (HBLK2 _ _ Hinb); lia.
- right; left. exists cid, pos. unfold frame_addr in *.
  destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF, Hfrs. cbn [app].
  split; [exact Hinf | lia].
- right; right. lia.
Qed.

(* WHERE THE NODE IS AFTER A SUCCESSFUL fuzz_realloc, as the reader states it (prhReader_at at the post state).
   Stated over the pieces the kit's SUCCESS arm gives (Lam = l1 ++ (p, k) :: l2, Lam2 = (res, nn) :: l1 ++ l2; the block
   list permuted with the new block in front of the old one's neighbours; frames and the layout kept), so the kids
   arm and the keys arm both use it (image B's constraint). The node is apart from the realloc's own
   block (HAPp), so its case of prhReader_at survives: a harness entry other than (p, k) is still in Lam2; a live
   allocator block that is not a harness block is still live (it is not the one realloc freed, and it cannot be the
   NEW block, since then the post state would hold it twice and its blocks would not be pairwise disjoint); a fake
   frame and the caller's extension are untouched. *)
Lemma grow_at_kept : forall ly S Hp (W : world segs) mem md ly2 S2 Hp2 (W2 : world segs) mem2 md2
  Lam l1 l2 regs e v p k nn res b1 b2,
  ARx ly S Hp W mem md -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
  (forall a kk, In (a, kk) Lam -> In (a - cf_head, kk + cf_head) (ablocks B ly S)) ->
  prhReader_at B ly S Lam regs e v 56 ->
  (forall x, pj_holdsR (p, k) x -> ~ (v <= x < v + 56)) ->
  Lam = l1 ++ (p, k) :: l2 ->
  ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 ->
  Permutation (ablocks B ly2 S2) ((res - cf_head, nn + cf_head) :: b1 ++ b2) ->
  frames S2 = frames S -> (forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos) ->
  (* the new block is NOT one of the blocks the realloc left alone (the allocator's own freshness: a live block is
     not handed out again). The kit's SUCCESS arm gives `~ In res (map fst (l1 ++ l2))` for the HARNESS blocks; this is
     the same fact for the allocator blocks, which the caller reads off the allocator's post. *)
  ~ In (res - cf_head, nn + cf_head) (b1 ++ b2) ->
  prhReader_at B ly2 S2 ((res, nn) :: l1 ++ l2) regs e v 56.
Proof.
intros ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam l1 l2 regs e v p k nn res b1 b2
  HAR HAR2 HLAM HAt HAPp HLam Eab Hperm Hfrs Hfa Hfresh.
pose proof cf_head_nonneg as Hh0.
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
(* the new block is in the post state *)
assert (Hnew2 : In (res - cf_head, nn + cf_head) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
(* an entry-state block other than the realloc's own is in the post state *)
assert (HKEEP : forall b m, In (b, m) (ablocks B ly S) -> (b, m) <> (p - cf_head, k + cf_head) ->
  In (b, m) (ablocks B ly2 S2)).
{ intros b m Hin Hne. apply (Permutation_in _ (Permutation_sym Hperm)). right.
  rewrite Eab in Hin. apply in_app_or in Hin as [Hb1 | [Heq | Hb2]];
    [apply in_or_app; left; exact Hb1 | exfalso; exact (Hne (eq_sym Heq)) | apply in_or_app; right; exact Hb2]. }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & Hnot & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- (* a harness block: not (p, k) (the node is apart from it), so it is in l1 ++ l2 *)
  left. exists a', k'. split; [|split; [exact H1 | exact H2]].
  right. rewrite HLam in Hin'. apply in_app_or in Hin' as [Hl1 | [Heq | Hl2]].
  + apply in_or_app; left; exact Hl1.
  + exfalso. injection Heq as <- <-. exact (HAPp v ltac:(unfold pj_holdsR; cbn [fst snd]; lia) ltac:(lia)).
  + apply in_or_app; right; exact Hl2.
- (* a live allocator block that is not a harness block *)
  assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (HBne : (b, m) <> (p - cf_head, k + cf_head)).
  { intros Heq. injection Heq as Eb Em. apply Hnot.
    replace (b + cf_head) with p by lia. replace (m - cf_head) with k by lia.
    rewrite HLam. apply in_or_app. right. left. reflexivity. }
  pose proof (HKEEP b m Hinb HBne) as Hin2.
  assert (Hin12 : In (b, m) (b1 ++ b2)).
  { rewrite Eab in Hinb. apply in_app_or in Hinb as [Hb1 | [Heq2 | Hb2]];
      [apply in_or_app; left; exact Hb1 | exfalso; apply HBne; rewrite <- Heq2; reflexivity
       | apply in_or_app; right; exact Hb2]. }
  assert (HNEW : (b, m) <> (res - cf_head, nn + cf_head)) by (intros Heq; apply Hfresh; rewrite <- Heq; exact Hin12).
  right; left. exists b, m. split; [exact Hin2|]. split; [|split; [exact H1 | exact H2]].
  intros Hin3. destruct Hin3 as [Heq | Hin4].
  + injection Heq as E1 E2. apply HNEW. f_equal; lia.
  + apply Hnot. rewrite HLam. apply in_app_or in Hin4 as [Hl1 | Hl2];
      [apply in_or_app; left; exact Hl1 | apply in_or_app; right; right; exact Hl2].
- right; right; left. exists cid, pos. rewrite Hfrs, Hfa. split; [exact Hinf | split; [exact H1 | exact H2]].
- right; right; right. split; [exact H1 | exact H2].
Qed.

(* the frame's shadow range covers the shadow of every byte of the frame: the frame is 32-aligned (alx_frames) and
   its length is 64 * 2 ^ cid, a multiple of 8 *)
Lemma frame_shadow_cover : forall fa fb x,
  fa mod 32 = 0 -> fb mod 8 = 0 -> 0 <= fb -> fa <= x < fa + fb ->
  shadow_addr fa <= SHADOW_OFF + x / 8 < shadow_addr fa + fb / 8.
Proof.
intros fa fb x Hal Hfb8 Hfb0 Hx. unfold shadow_addr.
pose proof (Z.div_mod fa 32 ltac:(lia)) as Hq. rewrite Hal, Z.add_0_r in Hq.
pose proof (Z.div_mod fb 8 ltac:(lia)) as Hr. rewrite Hfb8, Z.add_0_r in Hr.
set (q := fa / 32) in *. set (m := fb / 8) in *.
assert (Efa : fa / 8 = 4 * q)
  by (replace fa with (8 * (4 * q)) by lia; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
assert (Exq : x / 8 = 4 * q + (x - fa) / 8).
{ replace x with (8 * (4 * q) + (x - fa)) at 1 by lia. rewrite Z.mul_comm, Z.div_add_l by lia. lia. }
assert (Hlo : 0 <= (x - fa) / 8) by (apply Z.div_pos; lia).
assert (Hhi : (x - fa) / 8 < m) by (apply Z.div_lt_upper_bound; lia).
rewrite Efa, Exq. lia.
Qed.

(* THE NODE'S SHADOW ACROSS A fuzz_realloc CALL: the three law cases of prhReader_at at the POST state give it from
   the laws there (grow_v_shadow); the FAKE-FRAME case comes from the callee journal's frame clause, which keeps the
   frame's shadow bytes outside the callee's footprint - and the footprint is a heap block, below alloc_ceiling,
   while the shadow is an app address. NO extra premise: the frame's class cid is bounded below by the case itself
   (the node's 56 bytes lie inside the frame, and fs_frame_bytes cid = Z.shiftl 64 cid is at most 32 when cid < 0),
   so the lemma asks nothing that the kit's text does not give. *)
Lemma grow_v_shadow2 : forall ly S Hp (W : world segs) memc mdc ly2 S2 Hp2 (W2 : world segs) mem2 md2
  Lam2 peak2 cnt2 fail2 ran2 most2 own2 regs e v STK1 sp1 FP1 k1,
  ARx ly S Hp W memc mdc -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  prhReader_at B ly2 S2 Lam2 regs e v 56 ->
  ly_stk_lo ly2 <= spZ regs -> spZ regs + e <= ly_stk_hi ly2 ->
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF v 56 ->
  ajournal_xR (SK := SK) segs B PST ARx RW STK1 sp1 FP1 ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, inFP FP1 a -> app_addr a) ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF v 56.
Proof.
intros ly S Hp W memc mdc ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 regs e v STK1 sp1 FP1 k1
  HAR HAR2 HL2 HAt2 Hlo Hhi HRAc HJ HFPapp.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_frm HJ) as F4.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (grow_v_shadow ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 regs e v HAR2 HL2 HAt2 Hlo Hhi).
intros (cid & pos & Hinf2 & Hf1 & Hf2) x Hx.
assert (Hinf : In (cid, pos) (frames S)) by (rewrite Hfrs in Hinf2; cbn [app] in Hinf2; exact Hinf2).
(* the case itself bounds cid: the node's 56 bytes are inside the frame, and fs_frame_bytes cid = Z.shiftl 64 cid
   is at most 32 for a negative cid *)
assert (Hcid : 0 <= cid).
{ destruct (Z_le_gt_dec 0 cid) as [Hc | Hc]; [exact Hc | exfalso].
  assert (Hfb56 : 56 <= fs_frame_bytes cid) by lia.
  unfold fs_frame_bytes in Hfb56.
  rewrite <- (Z.opp_involutive cid), Z.shiftl_opp_r, Z.shiftr_div_pow2 in Hfb56 by lia.
  assert (Hpw2 : 2 <= 2 ^ (- cid))
    by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
  assert (Hdiv : 64 / 2 ^ (- cid) <= 32) by (apply Z.div_le_upper_bound; lia).
  lia. }
assert (Efa : frame_addr ly2 cid pos = frame_addr ly cid pos)
  by (unfold frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
rewrite Efa in Hf1, Hf2.
destruct (alx_frames segs B ARx LAWS ly S Hp W memc mdc cid pos HAR Hinf) as (Hal32 & _ & _ & _).
assert (Hfb8 : fs_frame_bytes cid mod 8 = 0).
{ rewrite fs_frame_bytes_eq by exact Hcid.
  replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia.
  first [apply Z_mod_mult | apply Z.mod_mul; lia]. }
pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
destruct (frame_shadow_cover (frame_addr ly cid pos) (fs_frame_bytes cid) x Hal32 Hfb8 Hfb0 ltac:(lia)) as (Hs1 & Hs2).
destruct (HRAc x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. unfold shadow_of_addr.
assert (Esh : SHADOW_OFF + x / 8 = shadow_addr x) by reflexivity.
destruct (alx_frames segs B ARx LAWS ly S Hp W memc mdc cid pos HAR Hinf) as (_ & Hiapp & _ & _).
apply (F4 cid pos (SHADOW_OFF + x / 8) Hinf).
- right. unfold in_zr. cbn [fst snd]. exact (conj Hs1 Hs2).
- intros Hin. pose proof (HFPapp _ Hin) as Happ. rewrite Esh in Happ.
  replace x with (frame_addr ly cid pos + (x - frame_addr ly cid pos)) in Happ by lia.
  pose proof (shadow_addr_in_band (frame_addr ly cid pos) (fs_frame_bytes cid) (x - frame_addr ly cid pos)
    Hiapp ltac:(lia)) as Hband.
  unfold app_addr, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in Happ, Hband.
  pose proof ASAN_CEIL_range as (CR & _). lia.
Qed.

(* grow_at_kept's twin for the MALLOC shape (the kit's prh_alloc_post SUCCESS arm, which grow's cap = 0 case takes: the
   kids pointer is NULL, so fuzz_realloc is fuzz_malloc): Lam2 = (res, nn) :: Lam and the block list GAINS the new
   block at its end. Same reading of the four cases of prhReader_at. The freshness premise is the block form of
   `~ In res (map fst Lam)`; the kit states the harness form today (ask of 2026-10-29 for the block form). *)
Lemma grow_at_kept0 : forall ly S Hp (W : world segs) mem md ly2 S2 Hp2 (W2 : world segs) mem2 md2
  Lam regs e v nn res,
  ARx ly S Hp W mem md -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prhReader_at B ly S Lam regs e v 56 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res - cf_head, nn + cf_head)] ->
  frames S2 = frames S -> (forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos) ->
  ~ In (res - cf_head, nn + cf_head) (ablocks B ly S) ->
  prhReader_at B ly2 S2 ((res, nn) :: Lam) regs e v 56.
Proof.
intros ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam regs e v nn res
  HAR HAR2 HAt Eab Hfrs Hfa Hfresh.
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & Hnot & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- left. exists a', k'. split; [right; exact Hin' | split; [exact H1 | exact H2]].
- right; left. exists b, m. split; [rewrite Eab; apply in_or_app; left; exact Hinb|].
  split; [|split; [exact H1 | exact H2]].
  intros [Heq | Hin4]; [|exact (Hnot Hin4)].
  injection Heq as E1 E2. apply Hfresh. replace (res - cf_head) with b by lia.
  replace (nn + cf_head) with m by lia. exact Hinb.
- right; right; left. exists cid, pos. rewrite Hfrs, Hfa. split; [exact Hinf | split; [exact H1 | exact H2]].
- right; right; right. split; [exact H1 | exact H2].
Qed.

(* ---- the NEW block of a successful fuzz_realloc / fuzz_malloc against grow's writes (shared
   with image A's walk) ---- *)

(* a pairwise relation over a list that holds y twice relates y to itself *)
Lemma grow_pairwise_dup {X} : forall (R : X -> X -> Prop) l (y : X) tl, pairwise R (l ++ y :: tl) -> In y l -> R y y.
Proof.
intros R l. induction l as [|z l IH]; intros y tl P Hin; [destruct Hin|].
cbn in P. destruct P as [F P]. destruct Hin as [<- | Hin].
- apply (proj1 (Forall_forall _ _) F). apply in_or_app. right. left. reflexivity.
- exact (IH y tl P Hin).
Qed.

(* the conclusion of the kit's lemma prh_alloc_fresh_append (lib/A/PRH_FnAlloc.v:255 at the cut 7cdbb61b5fa0), which
   takes NoDup of the post blocks' addresses; here from the allocator relation's laws instead. The APPEND equality of prh_alloc_post's SUCCESS arm (PRH_FnAlloc.v:234)
   would put the new block twice in the post state's block list if it were live before; the post state's blocks are
   pairwise disjoint (alx_sep) and the new one is at least one byte long (n is the request, 0 <= n). *)
Lemma grow_alloc_fresh_append : forall ly S ly' S' Hp' (W' : world segs) mem' md' res n,
  ARx ly' S' Hp' W' mem' md' -> 0 <= n ->
  ablocks B ly' S' = ablocks B ly S ++ [(res - cf_head, n + cf_head)] ->
  ~ In (res - cf_head, n + cf_head) (ablocks B ly S).
Proof.
intros ly S ly' S' Hp' W' mem' md' res n HAR Hn E Hin.
pose proof cf_head_nonneg as Hh0.
destruct (alx_sep _ _ _ LAWS _ _ _ _ _ _ HAR) as (Hpw & _).
rewrite E, map_app, <- app_assoc in Hpw. cbn [map app] in Hpw.
eapply grow_pairwise_dup in Hpw;
  [| apply in_map_iff; exists (res - cf_head, n + cf_head); split; [reflexivity | exact Hin]].
unfold zdisjoint in Hpw. cbn [fst snd] in Hpw.
assert (1 <= req_size (n + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (n + cf_head) 0); lia).
lia.
Qed.

(* WHERE THE NEW BLOCK IS, after a successful fuzz_realloc of the harness block (p, k): its allocator range holds no
   byte grow writes. It is an allocator block, so it lies below the frame. And it is apart from the node's 56 bytes
   wherever the node lies at the call state: a harness block other than (p, k) (the node is apart from (p, k)) and any
   other live allocator block stay live and are not the new block (the text's block freshness), so the post state's
   laws keep the two apart (sep_blocks_x); a live fake frame stays live (sep_block_frame_x at the post state); the
   caller's extension is above alloc_ceiling. The kids call and the keys call of both images use it. *)
Lemma grow_new_apart : forall FR ly S Hp (W : world segs) mem md ly2 S2 Hp2 (W2 : world segs) mem2 md2
  Lam peak cnt fail ran most own l1 l2 regs e v p k nn res b1 b2 x,
  0 <= FR <= 120 ->
  ARx ly S Hp W mem md -> ARx ly2 S2 Hp2 W2 mem2 md2 -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling + 128 <= spZ regs ->
  (forall y, pj_holdsR (p, k) y -> ~ (v <= y < v + 56)) ->
  Lam = l1 ++ (p, k) :: l2 ->
  ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 ->
  Permutation (ablocks B ly2 S2) ((res - cf_head, nn + cf_head) :: b1 ++ b2) ->
  frames S2 = frames S -> (forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos) ->
  ~ In (res - cf_head, nn + cf_head) (b1 ++ b2) ->
  res - cf_head <= x < res - cf_head + req_size (nn + cf_head) ->
  0 <= x < 2 ^ 64 /\ ~ grow_wr FR (spZ regs) v x.
Proof.
intros FR ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam peak cnt fail ran most own l1 l2 regs e v p k nn res b1 b2 x
  HFR HAR HAR2 HL HAt Hsp HAPp HLam Eab Hperm Hfrs Hfa Hfresh Hx.
pose proof HL as (_ & _ & HF & _).
pose proof cf_head_nonneg as Hh0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hnew2 : In (res - cf_head, nn + cf_head) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hnew2) as (_ & Hn4096 & Hnc & _).
split; [lia|]. unfold grow_wr. intros [Hw | Hw]; [lia|].
(* a block of b1 ++ b2 is live at the post state and is not the new one: the post state's laws keep them apart *)
assert (HFAR : forall b m, In (b, m) (b1 ++ b2) ->
  b + req_size m <= res - cf_head \/ res - cf_head + req_size (nn + cf_head) <= b).
{ intros b m Hin.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); right; exact Hin).
  assert (Hne : (b, m) <> (res - cf_head, nn + cf_head)) by (intros Heq; apply Hfresh; rewrite <- Heq; exact Hin).
  pose proof (sep_blocks_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR2 Hin2 Hnew2 Hne) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. exact Hd. }
(* a block of the call state other than the realloc's own is one of b1 ++ b2 *)
assert (HB12 : forall b m, In (b, m) (ablocks B ly S) -> (b, m) <> (p - cf_head, k + cf_head) -> In (b, m) (b1 ++ b2)).
{ intros b m Hin Hne. rewrite Eab in Hin. apply in_app_or in Hin as [Hb1 | [Heq | Hb2]];
    [apply in_or_app; left; exact Hb1 | exfalso; exact (Hne (eq_sym Heq)) | apply in_or_app; right; exact Hb2]. }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & Hnot & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- (* a harness block: not (p, k), whose bytes the node is apart from *)
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  assert (Hne : (a' - cf_head, k' + cf_head) <> (p - cf_head, k + cf_head)).
  { intros Heq. injection Heq as E1 E2.
    exact (HAPp v ltac:(unfold pj_holdsR; cbn [fst snd]; lia) ltac:(lia)). }
  pose proof (HFAR _ _ (HB12 _ _ Hb' Hne)) as Hd. lia.
- (* another live allocator block: not the realloc's own, which is a harness block *)
  assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (Hne : (b, m) <> (p - cf_head, k + cf_head)).
  { intros Heq. injection Heq as E1 E2. apply Hnot. replace (b + cf_head) with p by lia.
    replace (m - cf_head) with k by lia. rewrite HLam. apply in_or_app. right. left. reflexivity. }
  pose proof (HFAR _ _ (HB12 _ _ Hinb Hne)) as Hd. lia.
- (* a live fake frame, still live at the post state *)
  assert (Hinf2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hinf).
  pose proof (sep_block_frame_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ cid pos HAR2 Hnew2 Hinf2) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. rewrite Hfa in Hd. lia.
- (* the caller's extension, above alloc_ceiling *)
  lia.
Qed.

(* its twin for the MALLOC shape (prh_alloc_post's SUCCESS arm, which grow's cap = 0 case takes): the block list GAINS
   the new block, which was not live before (grow_alloc_fresh_append) *)
Lemma grow_new_apart0 : forall FR ly S Hp (W : world segs) mem md ly2 S2 Hp2 (W2 : world segs) mem2 md2
  Lam peak cnt fail ran most own regs e v nn res x,
  0 <= FR <= 120 ->
  ARx ly S Hp W mem md -> ARx ly2 S2 Hp2 W2 mem2 md2 -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling + 128 <= spZ regs ->
  0 <= nn -> ablocks B ly2 S2 = ablocks B ly S ++ [(res - cf_head, nn + cf_head)] ->
  frames S2 = frames S -> (forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos) ->
  res - cf_head <= x < res - cf_head + req_size (nn + cf_head) ->
  0 <= x < 2 ^ 64 /\ ~ grow_wr FR (spZ regs) v x.
Proof.
intros FR ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam peak cnt fail ran most own regs e v nn res x
  HFR HAR HAR2 HL HAt Hsp Hnn Eab Hfrs Hfa Hx.
pose proof HL as (_ & _ & HF & _).
pose proof cf_head_nonneg as Hh0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (grow_alloc_fresh_append ly S ly2 S2 Hp2 W2 mem2 md2 res nn HAR2 Hnn Eab) as Hfresh.
assert (Hnew2 : In (res - cf_head, nn + cf_head) (ablocks B ly2 S2))
  by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hnew2) as (_ & Hn4096 & Hnc & _).
split; [lia|]. unfold grow_wr. intros [Hw | Hw]; [lia|].
assert (HFAR : forall b m, In (b, m) (ablocks B ly S) ->
  b + req_size m <= res - cf_head \/ res - cf_head + req_size (nn + cf_head) <= b).
{ intros b m Hin.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; left; exact Hin).
  assert (Hne : (b, m) <> (res - cf_head, nn + cf_head)) by (intros Heq; apply Hfresh; rewrite <- Heq; exact Hin).
  pose proof (sep_blocks_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR2 Hin2 Hnew2 Hne) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. exact Hd. }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & Hnot & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  pose proof (HFAR _ _ Hb') as Hd. lia.
- assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  pose proof (HFAR _ _ Hinb) as Hd. lia.
- assert (Hinf2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hinf).
  pose proof (sep_block_frame_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ cid pos HAR2 Hnew2 Hinf2) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. rewrite Hfa in Hd. lia.
- lia.
Qed.

(* ---- what the KEYS call (an object's second fuzz_realloc) needs (shared with image A's walk):
   its call state is the kids call's post state, whose harness list no longer holds grow's entry slots, so the
   node's apartness from the callee's footprint is a premise (grow_slot_v at grow's ENTRY state gives it: the old
   keys block is an entry slot block) ---- *)

(* grow_v_kept with the footprint apartness given directly *)
Lemma grow_v_kept_fp : forall ly S Hp (W : world segs) memc mdc Lam peak cnt fail ran most own regs e v
  STK1 sp1 FP1 ly2 S2 Hp2 (W2 : world segs) mem2 md2 k1,
  ARx ly S Hp W memc mdc -> prh_ledger B ly S Hp W memc Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling + 128 <= spZ regs -> 4096 <= v -> v + 56 <= 2 ^ 64 ->
  (forall a, v <= a < v + 56 -> ~ in_img segs a) ->
  (forall a, spZ regs <= a < spZ regs + e -> apresent (w_H W) memc a) ->
  ajournal_xR (SK := SK) segs B PST ARx RW STK1 sp1 FP1 ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  sp1 <= spZ regs ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) ->
  forall a, v <= a < v + 56 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a /\ apresent (w_H W2) mem2 a.
Proof.
intros ly S Hp W memc mdc Lam peak cnt fail ran most own regs e v STK1 sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  HAR HL HAt Hsp Hv0 Hv64 Hoff Hpc HJ Hsp1 HnFP a Ha.
pose proof (ajxR_hi HJ) as G1. pose proof (ajxR_blk HJ) as G2. pose proof (ajxR_frm HJ) as G4.
pose proof (ajxR_gone HJ) as Hgone.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
pose proof (HnFP a Ha) as HnF.
assert (HTR : aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a -> apresent (w_H W) memc a ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a /\ apresent (w_H W2) mem2 a).
{ intros Hv Hpm. split; [exact Hv|]. eapply apresent_transfer; [lia | exact (Hoff a Ha) | exact Hv | exact Hpm]. }
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
assert (HBLK : forall p m, In (p, m) (ablocks B ly S) -> p <= v -> v + 56 <= p + req_size m ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a /\ apresent (w_H W2) mem2 a).
{ intros p m Hin Hpv1 Hpv2.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpr & _).
  apply HTR; [| exact (proj1 (Hpr a ltac:(lia)))].
  destruct (in_dec Hdec (p, m) (ablocks B ly2 S2)) as [Hin2 | Hout].
  - replace a with (p + (a - p)) by lia.
    apply (G2 p m (a - p) Hin Hin2); [lia |]. replace (p + (a - p)) with a by lia. exact HnF.
  - exfalso. apply HnF. replace a with (p + (a - p)) by lia. exact (Hgone p m (a - p) Hin Hout ltac:(lia)). }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & _ & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- pose proof HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  apply (HBLK _ _ Hb'); lia.
- assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply (HBLK _ _ Hinb); lia.
- destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ cid pos HAR Hinf) as (_ & _ & Hfp & _).
  apply HTR; [| exact (proj1 (Hfp a ltac:(lia)))].
  apply (G4 cid pos a Hinf); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnF].
- apply HTR; [apply G1; lia | apply Hpc; lia].
Qed.

(* grow_vloc2 with the footprint apartness given directly *)
Lemma grow_vloc2_fp : forall ly S Hp (W : world segs) memc mdc Lam peak cnt fail ran most own regs e v
  STK1 sp1 FP1 ly2 S2 Hp2 (W2 : world segs) mem2 md2 k1,
  prh_ledger B ly S Hp W memc Lam peak cnt fail ran most own -> prhReader_at B ly S Lam regs e v 56 ->
  ajournal_xR (SK := SK) segs B PST ARx RW STK1 sp1 FP1 ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) ->
  grow_vloc ly2 S2 regs e v.
Proof.
intros ly S Hp W memc mdc Lam peak cnt fail ran most own regs e v STK1 sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 HL HAt HJ HnFv.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_gone HJ) as Hgone.
pose proof cf_head_nonneg as Hh0.
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
assert (HBLK2 : forall p m, In (p, m) (ablocks B ly S) -> p <= v -> v + 56 <= p + req_size m ->
  grow_vloc ly2 S2 regs e v).
{ intros p m Hin Hpv1 Hpv2.
  destruct (in_dec Hdec (p, m) (ablocks B ly2 S2)) as [Hin2 | Hout].
  - left. exists p, m. split; [exact Hin2 | lia].
  - exfalso. apply (HnFv v ltac:(lia)). replace v with (p + (v - p)) by lia.
    exact (Hgone p m (v - p) Hin Hout ltac:(lia)). }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & _ & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- pose proof HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  apply (HBLK2 _ _ Hb'); lia.
- assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply (HBLK2 _ _ Hinb); lia.
- right; left. exists cid, pos. unfold frame_addr in *.
  destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF, Hfrs. cbn [app].
  split; [exact Hinf | lia].
- right; right. lia.
Qed.

(* the node's place survives a call that leaves the blocks, the frames and the frames' addresses alone (a NULL arm) *)
Lemma grow_at_eq : forall ly S ly' S' Lam regs e v n,
  ablocks B ly' S' = ablocks B ly S -> frames S' = frames S ->
  (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) ->
  prhReader_at B ly S Lam regs e v n -> prhReader_at B ly' S' Lam regs e v n.
Proof.
intros ly S ly' S' Lam regs e v n Eab Efr Efa H. unfold prhReader_at in *. rewrite Eab, Efr.
destruct H as [H | [H | [(cid & pos & Hin & H1 & H2) | H]]];
  [left; exact H | right; left; exact H | | right; right; right; exact H].
right; right; left. exists cid, pos. rewrite !Efa. split; [exact Hin | split; [exact H1 | exact H2]].
Qed.

(* two lists that are one swap apart up to order: x :: X ~ y :: Y with x <> y leaves a common rest R *)
Lemma grow_perm_swap2 {A} : forall (x y : A) (X Y : list A), x <> y -> Permutation (x :: X) (y :: Y) ->
  exists R, Permutation X (y :: R) /\ Permutation Y (x :: R).
Proof.
intros x y X Y Hne HP.
assert (Hy : In y X).
{ assert (Hin : In y (x :: X)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct Hin as [Heq | Hin]; [exfalso; exact (Hne Heq) | exact Hin]. }
apply in_split in Hy as (X1 & X2 & ->).
exists (X1 ++ X2). split; [apply Permutation_sym, Permutation_middle|].
apply Permutation_sym. apply (Permutation_cons_inv (a := y)).
eapply perm_trans; [apply perm_swap|]. eapply perm_trans; [|exact HP].
apply perm_skip. apply Permutation_middle.
Qed.

(* the shadow hull is closed under sub-ranges (YGcfHeadSh.v shadow_hull_vis_sub_cf, over YG0d's hull) *)
Lemma grow_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.

(* a live harness block's user bytes are addressable with a visible hull, by the harness-block shadow law at the
   state itself (AR_laws_x field 14): what prhReader_vis asks of a block a call left alone *)
Lemma grow_vis_law : forall ly S Hp (W : world segs) mem md a k,
  ARx ly S Hp W mem md -> In (a - cf_head, k + cf_head) (ablocks B ly S) -> In (a - cf_head) Hp -> 0 <= k ->
  prhReader_vis W mem a k.
Proof.
intros ly S Hp W mem md a k HAR Hb Hhp Hk.
pose proof cf_head_nonneg as Hh.
assert (Hq : 0 < req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); cbn; lia).
destruct (HSH ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hb Hhp) as (HBS & HHV).
replace (a - cf_head + cf_head) with a in HBS, HHV by lia.
split.
- apply (block_shadow_range _ _ a (req_size (k + cf_head) - cf_head) a k HBS); lia.
- intros Hk0. apply (grow_hull_sub _ a (req_size (k + cf_head) - cf_head) a k); [apply HHV; lia | lia | lia].
Qed.

(* ---- THE LIVE REQUESTS AND COUNTS of the post-implication texts (tgrow_specX and tfuzz_realloc_specX; stated by
   the header of lib/A/PRH_FnReader.v, its section THE LIVE COUNTS AT THE INNER CALLS):
   each post arm states
   `Permutation (rs_live (room_of_cf S')) (hlive_from (rs_live (room_of_cf S)) E)`, which follows from the arm's own
   blocks facts; the two inner calls' sec_cnt / ccnt24 premises follow from the text's pkR premises by pkR_prefix.
   rs_live (room_of_cf S) is map snd (blocks S) (CfRoomLivePreset.rs_live_blocks, by reflexivity), and ablocks only
   rewrites each block's address, so it is map snd (ablocks B ly S) at every layout. ---- *)
Local Notation RSL S := (PresetRoom.rs_live (YGcfRoom.room_of_cf S)).
Lemma grow_rs_live_ab : forall ly S, RSL S = map snd (ablocks B ly S).
Proof. intros ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.
(* hstep's realloc removes the FIRST request of the old size: a permutation of the list without the old block *)
Lemma grow_rm1_mid : forall z l1 l2, Permutation (PresetReqAt.rm1 z (l1 ++ z :: l2)) (l1 ++ l2).
Proof.
intros z l1 l2. induction l1 as [|y l1 IH]; cbn [app PresetReqAt.rm1].
- rewrite Z.eqb_refl. apply Permutation_refl.
- destruct (Z.eqb_spec y z) as [-> | Hne].
  + apply Permutation_sym, Permutation_middle.
  + apply perm_skip. exact IH.
Qed.
(* no allocator step: the blocks, so the live requests, are kept *)
Lemma grow_live_keep : forall ly S ly' S', ablocks B ly' S' = ablocks B ly S ->
  Permutation (RSL S') (PresetReqAt.hlive_from (RSL S) []).
Proof.
intros ly S ly' S' E. rewrite PresetReqAt.hlive_from_nil, (grow_rs_live_ab ly' S'), (grow_rs_live_ab ly S), E.
apply Permutation_refl.
Qed.
(* a realloc that moved its block (tfuzz_realloc_specX's success arm) *)
Lemma grow_live_re : forall ly S ly' S' b1 b2 p k res n,
  ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 ->
  Permutation (ablocks B ly' S') ((res - cf_head, n + cf_head) :: b1 ++ b2) ->
  Permutation (RSL S') (PresetReqAt.hlive_from (RSL S) [PresetReqAt.HRe (k + cf_head) (n + cf_head)]).
Proof.
intros ly S ly' S' b1 b2 p k res n E HP. rewrite (grow_rs_live_ab ly' S'), (grow_rs_live_ab ly S), E.
unfold PresetReqAt.hlive_from. cbn [fold_left PresetReqAt.hstep]. rewrite map_app. cbn [map snd].
eapply perm_trans; [exact (Permutation_map snd HP)|]. cbn [map snd]. apply perm_skip.
rewrite map_app. apply Permutation_sym, grow_rm1_mid.
Qed.
(* a malloc (realloc of a NULL array: prh_alloc_post's success arm) *)
Lemma grow_live_mal : forall ly S ly' S' res n,
  ablocks B ly' S' = ablocks B ly S ++ [(res - cf_head, n + cf_head)] ->
  Permutation (RSL S') (PresetReqAt.hlive_from (RSL S) [PresetReqAt.HMal (n + cf_head)]).
Proof.
intros ly S ly' S' res n E. rewrite (grow_rs_live_ab ly' S'), (grow_rs_live_ab ly S), E, map_app.
unfold PresetReqAt.hlive_from. cbn [fold_left PresetReqAt.hstep map snd].
apply Permutation_sym, Permutation_cons_append.
Qed.
(* two steps in a row *)
Lemma grow_live_trans : forall S1 S2 S3 E1 E2,
  Permutation (RSL S2) (PresetReqAt.hlive_from (RSL S1) E1) ->
  Permutation (RSL S3) (PresetReqAt.hlive_from (RSL S2) E2) ->
  Permutation (RSL S3) (PresetReqAt.hlive_from (RSL S1) (E1 ++ E2)).
Proof.
intros S1 S2 S3 E1 E2 H1 H2. rewrite PresetReqAt.hlive_from_app. eapply perm_trans; [exact H2|].
apply PresetReqAtNoMiss.hlive_from_perm. exact H1.
Qed.
(* a count is the same on a permutation *)
Lemma grow_cnt_perm : forall f l l', Permutation l l' -> PresetReqAt.cnt f l = PresetReqAt.cnt f l'.
Proof.
intros f l l' H. unfold PresetReqAt.cnt. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2].
- reflexivity.
- cbn [List.filter]. destruct (f x); cbn [length]; [rewrite IH; reflexivity | exact IH].
- cbn [List.filter]. destruct (f x), (f y); reflexivity.
- rewrite IH1; exact IH2.
Qed.
(* THE COUNT AT AN INNER CALL: the state after the first j events of the all-granted list E, from the text's pkR *)
Lemma grow_cnt_at : forall f S S' E j bound,
  Permutation (RSL S') (PresetReqAt.hlive_from (RSL S) (firstn j E)) ->
  Z.of_nat (PresetRun.pkR f (RSL S) E) <= bound ->
  Z.of_nat (PresetReqAt.cnt f (RSL S')) <= bound.
Proof.
intros f S S' E j bound HP Hk. rewrite (grow_cnt_perm f _ _ HP).
pose proof (PresetRun.pkR_prefix f E (RSL S) j). lia.
Qed.

(* ---- list facts the realloc arms need (image A's statements, lib/A/Prog/PwGrow.v :793-821 at
   r102-growA 07e5ec3b321e, moved here so A' and B' share one copy) ---- *)
(* a hidden head set without repeats loses one element up to order *)
Lemma perm_remove_nodup : forall (l : list Z) x, List.NoDup l -> In x l ->
  Permutation l (x :: remove Z.eq_dec x l).
Proof.
induction l as [|y l IH]; intros x HN Hin; [destruct Hin|].
apply NoDup_cons_iff in HN as (Hny & HN').
cbn [remove]. destruct (Z.eq_dec x y) as [Exy | Hne].
- subst y. rewrite notin_remove by exact Hny. apply Permutation_refl.
- destruct Hin as [Eyx | Hin]; [exfalso; apply Hne; symmetry; exact Eyx|].
  eapply perm_trans; [apply perm_skip, (IH x HN' Hin)|]. apply perm_swap.
Qed.
Lemma ledger_hp_nodup : forall ly S Hp (W : world segs) mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> List.NoDup Hp.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own (_ & HND & _ & HP).
apply NoDup_ListNoDup in HND.
apply (Permutation_NoDup (Permutation_sym HP)).
replace (map (fun ak : Z * Z => fst ak - cf_head) Lam) with (map (fun a => a - cf_head) (map fst Lam))
  by (rewrite map_map; reflexivity).
clear HP. revert HND. generalize (map fst Lam) as l0.
induction l0 as [|a l IH]; intros HND; cbn [map]; [constructor|].
apply NoDup_cons_iff in HND as (Hna & HN'). apply NoDup_cons; [|exact (IH HN')].
intros Hin. apply in_map_iff in Hin as (b & Hb & Hbin). assert (Eb : b = a) by lia. subst b. exact (Hna Hbin).
Qed.
Lemma bytes_at_prefix : forall (W : world segs) mem p l1 l2, bytes_at W mem p (l1 ++ l2) -> bytes_at W mem p l1.
Proof.
intros W mem p l1 l2 HB j Hj. destruct (HB j ltac:(rewrite length_app; lia)) as [Hv Hr].
rewrite app_nth1 in Hv, Hr by lia. exact (conj Hv Hr).
Qed.

(* THE WORLD-FREE REFUSAL EVIDENCE (the move's shape note sec. 5.1: grow's two refused arms state only what a refusal
   changes, with no world) from the MALLOC refusal leaf, which is not primed and gives it: blocks and chunks kept
   (YG0dcf.v malloc_cf_null_post's :301), the request from the primary, its class exhausted (:304). grow's cap = 0
   calls are realloc (NULL, n), i.e. prh_alloc_post's refused arm 2, which carries this leaf. *)
Lemma grow_null_wf : forall ly S Hp (W : world segs) regsc memc mdc n S' Wc cc,
  YG0dcf.malloc_cf_null_post segs B ly S Hp W regsc memc mdc n (PNull, S') Wc cc ->
  blocks S' = blocks S /\ st_chunks S' = st_chunks S /\ from_primary n = true /\
  YG00cf.exh_mem_cf S' (chunk_class n) = true.
Proof.
intros ly S Hp W regsc memc mdc n S' Wc cc (_ & ly' & regs' & mem' & md' & _ & _ & _ & _ & Hb & Hc & _ & _ & Hfp & Hex & _).
cbn [snd] in Hb, Hc, Hex. exact (conj Hb (conj Hc (conj Hfp Hex))).
Qed.

(* ---- THE HULL (the threaded allocator hull premise, route (b); lib/Spec/PresetHullBudget.v): grow's text takes
   hull_budget S over its ALL-GRANTED events prhPg_evs .. [] (the kids realloc's event, then for an object the keys
   realloc's) and states hull_used S S' over the same list; each realloc text takes the budget of its one event and
   states its use. The walk pays the kids call from grow's budget, the keys call from what the kids call left, and
   composes the uses. ---- *)
(* a realloc call's event list, at grow's request k * cap' from its old block of k * cap bytes: prhPg_ev's form, when
   the old pointer is NULL exactly at cap = 0 (pj_slots_atR) *)
Lemma grow_hull_ev : forall (p k cap : Z), (p = 0 <-> cap = 0) ->
  (if p =? 0 then [PresetReqAt.HMal (k * cap2R cap + cf_head)]
   else [PresetReqAt.HRe (k * cap + cf_head) (k * cap2R cap + cf_head)]) = [prhPg_ev k cap].
Proof.
intros p k cap Hpc. unfold prhPg_ev.
destruct (Z.eqb_spec p 0) as [Hp | Hp]; destruct (Z.eqb_spec cap 0) as [Hc | Hc]; try reflexivity; exfalso; tauto.
Qed.
(* grow's all-granted list at n = cap: the kids event, then the keys event for an object *)
Lemma grow_hull_evs : forall (o : bool) cap,
  prhPg_evs o cap cap [] = [prhPg_ev 56 cap] ++ (if o then [prhPg_ev 8 cap] else []).
Proof. intros o cap. unfold prhPg_evs. rewrite Z.ltb_irrefl. cbn [nth]. destruct o; reflexivity. Qed.
(* the kids call's budget, from grow's *)
Lemma grow_hull_kids : forall S (o : bool) cap,
  PresetHullBudget.hull_budget S (prhPg_evs o cap cap []) -> PresetHullBudget.hull_budget S [prhPg_ev 56 cap].
Proof.
intros S o cap H. rewrite grow_hull_evs in H.
apply (PresetHullBudget.hull_budget_infix S S [] [prhPg_ev 56 cap] (if o then [prhPg_ev 8 cap] else []));
  [exact H | apply PresetHullBudget.hull_used_refl].
Qed.
(* the keys call's budget, from grow's less the kids call's use *)
Lemma grow_hull_keys : forall S S1 cap,
  PresetHullBudget.hull_budget S (prhPg_evs true cap cap []) ->
  PresetHullBudget.hull_used S S1 [prhPg_ev 56 cap] -> PresetHullBudget.hull_budget S1 [prhPg_ev 8 cap].
Proof.
intros S S1 cap H U. rewrite grow_hull_evs in H. exact (PresetHullBudget.hull_budget_app S S1 _ _ H U).
Qed.
(* the post's use: one call (an array, or an arm that stops after the kids call) or both *)
Lemma grow_hull_one : forall S S1 (o : bool) cap,
  PresetHullBudget.hull_used S S1 [prhPg_ev 56 cap] -> PresetHullBudget.hull_used S S1 (prhPg_evs o cap cap []).
Proof.
intros S S1 o cap U. rewrite grow_hull_evs.
exact (PresetHullBudget.hull_used_infix S S1 [] [prhPg_ev 56 cap] (if o then [prhPg_ev 8 cap] else []) U).
Qed.
Lemma grow_hull_two : forall S S1 S2 cap,
  PresetHullBudget.hull_used S S1 [prhPg_ev 56 cap] -> PresetHullBudget.hull_used S1 S2 [prhPg_ev 8 cap] ->
  PresetHullBudget.hull_used S S2 (prhPg_evs true cap cap []).
Proof.
intros S S1 S2 cap U1 U2. rewrite grow_hull_evs. exact (PresetHullBudget.hull_used_app S S1 S2 _ _ U1 U2).
Qed.
(* no call (n < cap): the allocator state is the entry's *)
Lemma grow_hull_none : forall S (o : bool) n cap, n < cap -> PresetHullBudget.hull_used S S (prhPg_evs o n cap []).
Proof. intros S o n cap _. apply PresetHullBudget.hull_used_refl. Qed.

(* ---- THE OUTCOME OF AN INJECTED READING at grow's kids-refused arm (the kit's dead-parse round; the proof is the kit
   owner's own probe of this link, adapted): at the model's grant list okk (fail - cnt) with the chosen failure inside
   grow's window, the list starts
   with the kids realloc's event, and the kids realloc's own OUTCOME (the leaf's text) says the instance granted there,
   contradicting the refused result. ---- *)
Lemma grow_okk_nth : forall k j, (j < k)%nat -> nth j (PresetReqAt.okk k) true = true.
Proof.
intros k j H. unfold PresetReqAt.okk. revert j H.
induction k as [|k IH]; intros j H; [lia|]. destruct j as [|j]; [reflexivity|].
cbn [repeat app nth]. apply IH. lia.
Qed.
Lemma grow_excl_of_leaf : forall (b : bool) (n cap cnt fail : Z) (S : astate) (res : Z),
  n = cap -> cnt <> fail -> res = 0 ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     PRH_Base.prh_run_at sm x os i [prhPg_ev 56 cap] ->
     PRH_Base.prh_cons_from sm x os i (length [prhPg_ev 56 cap]) -> cnt <> fail -> res <> 0) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs b n cap (PresetReqAt.okk (Z.to_nat (fail - cnt)))) ->
    PRH_Base.prh_cons_from sm x os i (length (prhPg_evs b n cap (PresetReqAt.okk (Z.to_nat (fail - cnt))))) ->
    cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPg_gtrace b n cap)) -> False.
Proof.
intros b n cap cnt fail S res Heq Hcf Hres HLEAF sm x os i H0 hist Hpos Hrun Hcons Hwin.
assert (E : prhPg_evs b n cap (PresetReqAt.okk (Z.to_nat (fail - cnt))) =
  [prhPg_ev 56 cap] ++
  (if b && nth 1 (PresetReqAt.okk (Z.to_nat (fail - cnt))) true then [prhPg_ev 8 cap] else [])).
{ unfold prhPg_evs. replace (n <? cap) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite grow_okk_nth by lia. reflexivity. }
rewrite E in Hrun, Hcons. apply PRH_Base.prh_run_at_app_iff in Hrun as (Hrun1 & _).
rewrite length_app in Hcons. apply PRH_Base.prh_cons_from_app_iff in Hcons as (Hcons1 & _).
exact (HLEAF sm x os i H0 hist Hpos Hrun1 Hcons1 Hcf Hres).
Qed.

End g.

(* the window characterization of a symbolic memory with grow's regions (Usp / Uv the values of the sp / a0 atoms in
   the state's environment) *)
Ltac grow_wr_tac Usp Uv :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?Uv in Hr;
           unfold grow_wr; lia |]);
  contradiction.

