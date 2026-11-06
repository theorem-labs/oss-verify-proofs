(* preset_base64_decode (fs.asan 0x8481c), part L of the Theorem Labs lane walk (a Theorem Labs lane), helper a Theorem Labs lane: the memory lemmas
   the loop needs at its cuts (contract (internal path), statements copied verbatim):
   (1) decLB_q / decLB_qw: the decode block q (dec_head's new block (q - 16, n + 16)): aligned, below alloc_ceiling, in
       application memory, not an image byte, new in this call (AR's pairwise separation of ablocks), writable;
   (2) decLB_text: the text and its NUL, in application memory and apart from the decode block (wsrc_kept: an entry
       block, separated from the decode block by AR, or an FS_RO_STRS entry, an image byte);
   (3) decLB_memf / decLB_keep / decLB_store: dec_head's memory conjuncts (FSW_dec_L0.decL_memf) and their transport
       over a memory change inside a stack window [lo, hi) below the entry sp, plus the store of the next decoded byte at
       q + n: every byte decL_memf reads (block head, block shadow, alloc.c statics, *lenp, the window [sp, ot), the
       text with the rest of its NUL's word, the shadow band, the read-only image, the decoded bytes) is below
       alloc_ceiling or at or above sp, and none is in the decode block's unwritten tail [q + n, q + d_n);
   (4) decLB_g64: memchr (g_b64, c, 65)'s premises, from fs_img_facts at the cut (cstr_ok of FS_RO_STRS' g_b64 entry on
       the unpoisoned memory), carried to the raw memory (no user-poisoned shadow byte covers an image byte) and then
       to the memory of the call;
   (5) decLB_lenp: *lenp on the caller's real stack: AR's zero stack shadow (FSW_put.v:177-211's pattern) and the
       journal's present window.
   SCRATCH during the walk (owner a Theorem Labs lane); a Theorem Labs lane integrates it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_dec_defs FSW_dec_L0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- fs.asan's image: its four PT_LOAD segments cover [0x10000, 0x5fd000) without a gap (MEASURED: segments
   (0x10000, 0x20000) (0x30000, 0x6f000) (0x9f000, 0x2000) (0xa1000, 0x55c000), the boundaries A/AD1y.v in_img_hull
   splits at) ---- *)
Lemma decLB_in_img : forall a, 0x10000 <= a < 0x5fd000 -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (HC : forall lo hi,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  lo <= a < hi -> in_img tfibsegs a).
{ intros lo hi Hb Hr. apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia]. }
destruct (Z.lt_ge_cases a 0x30000); [apply (HC 0x10000 0x30000); [vm_compute; reflexivity | lia]|].
destruct (Z.lt_ge_cases a 0x9f000); [apply (HC 0x30000 0x9f000); [vm_compute; reflexivity | lia]|].
destruct (Z.lt_ge_cases a 0xa1000); [apply (HC 0x9f000 0xa1000); [vm_compute; reflexivity | lia]|].
apply (HC 0xa1000 0x5fd000); [vm_compute; reflexivity | lia].
Qed.
(* an 8-byte image cell (the two shadow-base cells) is apart from every non-image byte *)
Lemma decLB_cell_apart : forall c a, 0x10000 <= c -> c + 8 <= 0x5fd000 -> ~ in_img tfibsegs a ->
  a + 1 <= c \/ c + 8 <= a.
Proof.
intros c a H1 H2 Hn. destruct (Z.lt_ge_cases a c); [left; lia|].
destruct (Z.lt_ge_cases a (c + 8)); [|right; lia]. exfalso. apply Hn. apply decLB_in_img. lia.
Qed.
(* the read-only image bytes (a non-writable segment or the relro range) *)
Lemma decLB_ro_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
apply decLB_in_img. unfold FS_RLO, FS_RHI in Hr. lia.
Qed.
(* every FS_RO_STRS entry, its NUL and the rest of the NUL's word lie in .rodata below 0x22000 *)
Lemma decLB_ro_strs : forall s l, In (s, l) FS_RO_STRS -> 0x20000 <= s /\ s + Z.of_nat (length l) + 8 <= 0x22000.
Proof.
intros s l H.
assert (Hb : forallb (fun r => (0x20000 <=? fst r) && (fst r + Z.of_nat (length (snd r)) + 8 <=? 0x22000)) FS_RO_STRS
  = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb (s, l) H) as X. cbn [fst snd] in X.
apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

(* ---- the decoded bytes so far fit the block: six_bytes six has 6 * |six| / 8 bytes, |six| <= |tb| ---- *)
Lemma decLB_six_len : forall six,
  Z.of_nat (length (WriterSpec.six_bytes six)) <= Z.of_nat (length six) / 4 * 3 + 2.
Proof.
fix IH 1. intros [|a [|b [|c [|d r]]]]; cbn [WriterSpec.six_bytes length]; try (Z.div_mod_to_equations; lia).
specialize (IH r). Z.div_mod_to_equations. lia.
Qed.
Lemma decLB_nbytes : forall six (tb : list Z), (length six <= length tb)%nat ->
  Z.of_nat (length (WriterSpec.six_bytes six)) < dec_size tb.
Proof.
intros six tb H. pose proof (decLB_six_len six) as X. unfold dec_size.
assert (Z.of_nat (length six) / 4 <= Z.of_nat (length tb) / 4) by (apply Z.div_le_mono; lia). lia.
Qed.

(* ---- reading through aview: equal aview gives equal bytes (val_mem) and, off the image, equal writability ---- *)
Lemma decLB_val_mem : forall (H : word -> bool) (m1 m2 : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> aview tfibsegs H m2 (a + Z.of_nat k) = aview tfibsegs H m1 (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict H m1) a n v -> val_mem tfibsegs (mrestrict H m2) a n v.
Proof.
intros H m1 m2 a n v HA Hv k Hk. rewrite (mbyte_of_aview tfibsegs H H m1 m2 _ (HA k Hk)). exact (Hv k Hk).
Qed.
Lemma decLB_wr_eq : forall (H : word -> bool) (m1 m2 : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a ->
  (writable_at tfibsegs (mrestrict H m1) a <-> writable_at tfibsegs (mrestrict H m2) a).
Proof.
intros H m1 m2 a Ha Hn X.
assert (EQ : mrestrict H m2 (Z_to_bv 64 a) = mrestrict H m1 (Z_to_bv 64 a)).
{ unfold aview, mbyte in X. rewrite (seg_rom_none tfibsegs a Ha Hn) in X.
  destruct (mrestrict H m2 (Z_to_bv 64 a)) as [b2|], (mrestrict H m1 (Z_to_bv 64 a)) as [b1|]; cbn in X;
    try discriminate X; [|reflexivity].
  injection X as X. f_equal. apply bv_eq. exact X. }
unfold writable_at, wview. rewrite EQ. reflexivity.
Qed.

Section L3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the image facts (FSH_Rt.v:73-76): a constant fact about B every lane takes as a Section hypothesis; it gives
   rom_view and cstr_ok of g_b64's 64 letters + NUL at every AR state *)
Hypothesis HIMG : fs_img_facts tfibsegs B.

(* ---- generic transports ---- *)
(* a C string read through the memory: equal bytes on its NUL's word span and on the shadow band carry cstr_ok *)
Lemma decLB_cstr_agree : forall (W : world tfibsegs) m1 m2 p l,
  (forall a, p <= a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) ->
  (forall a, SHADOW_OFF <= a < kHighMemBeg -> aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) ->
  cstr_ok tfibsegs W m1 p l -> cstr_ok tfibsegs W m2 p l.
Proof.
intros W m1 m2 p l AD AS H.
pose proof asan_consts as (C1 & _).
pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)) as Hm.
unfold cstr_ok, cstr in H |- *.
destruct H as ((Hg & Hnz) & H4 & Hc & H32 & Ham & Hra & Hhv & Htl).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p _ Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). apply AD. lia. }
split; [exact H4|]. split; [exact Hc|]. split; [exact H32|]. split; [exact Ham|].
split.
{ intros x Hx. destruct (Hra x Hx) as (s & Hs1 & Hs2). exists s. split; [|exact Hs2].
  rewrite AS; [exact Hs1|]. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg. lia. }
split.
{ intros s Hs. rewrite AS; [exact (Hhv s Hs)|]. unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *. lia. }
intros a Ha. rewrite AD; [exact (Htl a Ha)|]. lia.
Qed.

(* ---- the unpoisoned memory equals the raw one at an application address (FSupoison.ush_facts: a user-poisoned
   shadow byte lies in [SHADOW_OFF, kHighMemBeg)) and at the shadow of an image byte or of a byte above alloc_ceiling
   (ush_granule: it is the shadow of a granule of a live block, below alloc_ceiling and off the image) ---- *)
Lemma decLB_unp : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> (a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a H Ha Hb. apply unpoison_out. rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_facts tfibsegs B ly S U W mem md a H E) as (_ & U1 & U2). lia.
Qed.
Lemma decLB_aview_unp : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> (a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha Hb. apply (aview_at tfibsegs). exact (decLB_unp ly S U W mem md a H Ha Hb).
Qed.
Lemma decLB_ush : forall ly S U (W : world tfibsegs) mem md x,
  AR tfibsegs B ly S W (unpoison U mem) md -> upoison_ok B ly S U -> 0 <= x ->
  (in_img tfibsegs x \/ alloc_ceiling <= x) -> in_ush U (shadow_of_addr SHADOW_OFF x) = false.
Proof.
intros ly S U W mem md x HAR HOK Hx0 Hx.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (in_ush U (shadow_of_addr SHADOW_OFF x)) eqn:EU; [exfalso|reflexivity].
destruct (ush_granule B ly S U _ HOK EU) as (g & p & m & Hblk & Hg8 & Hgs & Hgpb & Hgn).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p m HAR Hblk) as (_ & _ & Hpceil & _ & _ & _ & HmM).
pose proof (req_size_pos m ltac:(lia)) as (RQ1 & RQ2).
pose proof (Z.mul_div_le (req_size m) 8 ltac:(lia)) as RQ3.
unfold shadow_addr, shadow_of_addr in Hgs.
assert (Hdiv : g / 8 = x / 8) by lia.
pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)).
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
destruct Hx as [Hi | Hc].
- apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md p m x HAR Hblk); [lia | exact Hi].
- lia.
Qed.

(* ---- the entry's stack facts ---- *)
Lemma decLB_sp : forall d, dec_entry_ok B d ->
  alloc_ceiling + 112 <= d_sp d /\ d_sp d <= d_ot d /\ d_ot d <= 2 ^ 47.
Proof.
intros d HE.
assert (HSTK : 112 <= STK_preset_base64_decode) by (vm_compute; discriminate).
destruct HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (_ & Hsp1 & Hsp2 & _).
pose proof (proj1 HPRE) as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
unfold d_sp. destruct HPL as [(_ & H1 & H2 & _ & H4 & _) | (_ & Hot & _)]; lia.
Qed.

(* ---- the decode block (q - 16, n + 16): dec_head's new block ---- *)
Lemma decLB_blk : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  In (q - HEAD, d_n d + HEAD) (ablocks B lyc Sc) /\ req_size (d_n d + HEAD) = d_n d + HEAD /\
  q mod 16 = 0 /\ 4096 + HEAD <= q /\ 0 < d_n d /\ q + d_n d <= alloc_ceiling /\
  (q + d_n d <= kLowShadowBeg \/ kHighMemBeg <= q - HEAD) /\
  (forall a, q - HEAD <= a < q + d_n d -> ~ in_img tfibsegs a) /\
  ~ In (q - HEAD, d_n d + HEAD) (ablocks B (d_ly d) (d_S d)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HH as (_ & HARU & _ & _ & _ & Hab & Hq & Hrb & _).
destruct HARU as (HARc & _ & _).
destruct Hrb as (Hin & Hq16 & Hn & _).
assert (RQ : req_size (d_n d + HEAD) = d_n d + HEAD)
  by (unfold req_size, HEAD; destruct (Z.eqb_spec (d_n d + 16) 0); lia).
destruct (al_blocks _ _ LAWS lyc Sc Wc (unpoison Uc memc) mdc (q - HEAD) (d_n d + HEAD) HARc Hin)
  as (_ & _ & Hceil & Happ & _ & Hpw & _).
rewrite RQ in Hceil, Happ. unfold in_app in Happ.
split; [exact Hin|]. split; [exact RQ|]. split; [exact Hq16|]. split; [exact Hq|]. split; [exact Hn|].
split; [unfold HEAD in *; lia|].
split; [destruct Happ as (_ & [X | (X & _)]); [left | right]; unfold HEAD in *; lia|].
split.
{ intros a Ha. apply (blk_img tfibsegs B LAWS lyc Sc Wc (unpoison Uc memc) mdc (q - HEAD) (d_n d + HEAD) a HARc Hin).
  rewrite RQ. unfold HEAD in *. lia. }
intros X. apply in_split in X as (l1 & l2 & E).
assert (E2 : map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B lyc Sc) =
  map (fun b : Z * Z => (fst b, req_size (snd b))) l1 ++ (q - HEAD, req_size (d_n d + HEAD)) ::
  map (fun b : Z * Z => (fst b, req_size (snd b))) l2 ++ (q - HEAD, req_size (d_n d + HEAD)) :: []).
{ rewrite Hab, E, <- app_assoc, !map_app. reflexivity. }
pose proof (YCbq.pairwise_In2 zdisjoint _ _ _ _ _ _ Hpw E2) as Z. unfold zdisjoint in Z. cbn [fst snd] in Z.
rewrite RQ in Z. unfold HEAD in *. lia.
Qed.

(* (1) the decode block: aligned, below alloc_ceiling, in application memory (not the shadow band), not an image byte,
   new in this call (so a byte of it is a tmp-block byte of the journal), its user bytes writable at any memory with ARU,
   and apart from the two shadow-base cells of the image *)
Lemma decLB_q : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  q mod 16 = 0 /\ 4096 + HEAD <= q /\ q + d_n d <= alloc_ceiling /\ 1 <= d_n d /\
  (q + d_n d <= SHADOW_OFF \/ kHighMemBeg <= q) /\
  ~ In (q - HEAD, d_n d + HEAD) (ablocks B (d_ly d) (d_S d)) /\
  (forall a, q <= a < q + d_n d ->
     ~ YG0d.in_img tfibsegs a /\ in_tmp_block (ablocks B (d_ly d) (d_S d)) (ablocks B lyc Sc) a /\
     (a + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= a) /\
     (a + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= a)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH.
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & Happ & NI & NIN).
split; [exact Hq16|]. split; [exact Hq|]. split; [exact Hqc|]. split; [lia|].
split; [unfold kLowShadowBeg, SHADOW_OFF, HEAD in *; lia|].
split; [exact NIN|].
intros a Ha.
assert (Hni : ~ in_img tfibsegs a) by (apply NI; unfold HEAD; lia).
split; [exact Hni|].
split; [exists (q - HEAD), (d_n d + HEAD); split; [exact Hin|]; split; [exact NIN|]; rewrite RQ; unfold HEAD; lia|].
split; apply decLB_cell_apart; try exact Hni;
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address; lia.
Qed.
Lemma decLB_qw : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc2 mdc2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  ARU tfibsegs B lyc Sc Uc Wc memc2 mdc2 ->
  forall a, q <= a < q + d_n d -> writable_at tfibsegs (mrestrict (w_H Wc) memc2) a.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc2 mdc2 HE HH HARU2 a Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & Happ & NI & NIN).
pose proof HARU2 as (HAR2 & _ & _).
destruct (al_blocks _ _ LAWS lyc Sc Wc (unpoison Uc memc2) mdc2 (q - HEAD) (d_n d + HEAD) HAR2 Hin)
  as (_ & _ & _ & _ & Hpr & _ & _).
rewrite RQ in Hpr.
destruct (Hpr a ltac:(unfold HEAD; lia)) as (Hp & _).
apply (apresent_writable tfibsegs).
destruct Hp as (Hh & b & Hb). split; [exact Hh|]. exists b.
assert (Happ' : a < SHADOW_OFF \/ kHighMemBeg <= a) by (unfold kLowShadowBeg, SHADOW_OFF, HEAD in *; lia).
rewrite <- (decLB_unp lyc Sc Uc Wc memc2 mdc2 a HARU2 ltac:(unfold HEAD in *; lia) Happ'). exact Hb.
Qed.

(* ---- where the text lies: an entry block apart from the decode block (AR separation; the decode block is 16-aligned,
   so it also clears the rest of the NUL's 8-byte word), or an FS_RO_STRS entry (an image byte) ---- *)
Lemma decLB_tsite : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  forall a, d_text d <= a < d_text d + Z.of_nat (length (d_tb d)) - (d_text d + Z.of_nat (length (d_tb d))) mod 8 + 8 ->
    ~ (q - HEAD <= a < q + d_n d) /\
    (a <= d_text d + Z.of_nat (length (d_tb d)) ->
       (a + 1 <= kLowShadowBeg \/ kHighMemBeg <= a) /\ (~ in_img tfibsegs a \/ a < 0x22000)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH a Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & Happq & NIq & NIN).
pose proof HH as (_ & HARU & _ & _ & _ & Hab & _). destruct HARU as (HARc & _ & _).
destruct HE as (_ & _ & _ & _ & _ & Hcs & Hws & _).
pose proof Hcs as (_ & Ht4096 & Htc & _).
pose proof (Z.mod_pos_bound (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hm.
pose proof (Z.div_mod (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hdm.
pose proof (Z.div_mod q 16 ltac:(lia)) as Hqdm.
assert (BLK : forall b m, In (b, m) (ablocks B (d_ly d) (d_S d)) -> b <= d_text d ->
  d_text d + Z.of_nat (length (d_tb d)) + 1 <= b + m ->
  ~ (q - HEAD <= a < q + d_n d) /\
  (a <= d_text d + Z.of_nat (length (d_tb d)) ->
     (a + 1 <= kLowShadowBeg \/ kHighMemBeg <= a) /\ (~ in_img tfibsegs a \/ a < 0x22000))).
{ intros b m Hbm Hb1 Hb2.
  assert (Hbmc : In (b, m) (ablocks B lyc Sc)) by (rewrite Hab; apply in_or_app; left; exact Hbm).
  assert (Hne : (b, m) <> (q - HEAD, d_n d + HEAD)) by (intros X; rewrite X in Hbm; exact (NIN Hbm)).
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc Wc (unpoison Uc memc) mdc b m (q - HEAD) (d_n d + HEAD)
    HARc Hbmc Hin Hne) as Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite RQ in Hsep.
  destruct (al_blocks _ _ LAWS lyc Sc Wc (unpoison Uc memc) mdc b m HARc Hbmc)
    as (Hb16 & Hb4096 & Hbc & Happ & _ & _ & HmM).
  pose proof (req_size_pos m ltac:(lia)) as (RQ1 & RQ2).
  unfold in_app in Happ.
  split; [unfold HEAD in *; lia|].
  intros Hat. split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|]. left.
  apply (blk_img tfibsegs B LAWS lyc Sc Wc (unpoison Uc memc) mdc b m a HARc Hbmc). lia. }
destruct Hws as [(Hnil & _) | [(p & kk & Hp0 & Hrb' & Hpt & Htp) | [(p & kk & Hpne & Hinp & Hpt & Htp & _) | (l & Hinl & Hll)]]].
- exfalso. apply app_eq_nil in Hnil as [_ X]. discriminate X.
- destruct Hrb' as (Hinp & Hp16 & Hkk & _). rewrite length_app in Htp. cbn [length] in Htp.
  apply (BLK (p - HEAD) (kk + HEAD) Hinp); unfold HEAD; lia.
- rewrite length_app in Htp. cbn [length] in Htp. apply (BLK p kk Hinp); lia.
- rewrite length_app in Hll. cbn [length] in Hll. change (Nat.succ (length l)) with (S (length l)) in Hll.
  destruct (decLB_ro_strs (d_text d) l Hinl) as (R1 & R2).
  split.
  + intros X. apply (NIq a X). apply decLB_in_img. lia.
  + intros Hat. split; [unfold kLowShadowBeg; lia | right; lia].
Qed.

(* (2) the text and its NUL: in application memory, apart from the decode block and the two shadow-base cells *)
Lemma decLB_text : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  4096 <= d_text d /\ d_text d + Z.of_nat (length (d_tb d)) + 1 <= alloc_ceiling /\
  (forall a, d_text d <= a <= d_text d + Z.of_nat (length (d_tb d)) ->
     ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416) /\
     ~ (q - HEAD <= a < q - HEAD + req_size (d_n d + HEAD)) /\
     (a + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= a) /\
     (a + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= a)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH.
pose proof HE as (_ & _ & _ & _ & _ & Hcs & _). pose proof Hcs as (_ & Ht4096 & Htc & _).
split; [exact Ht4096|]. split; [exact Htc|].
intros a Ha.
pose proof (Z.mod_pos_bound (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hm.
destruct (decLB_tsite d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH a ltac:(lia)) as (T1 & T2).
destruct (T2 ltac:(lia)) as (T3 & T4).
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (_ & RQ & _).
split; [unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia|].
split; [rewrite RQ; unfold HEAD in *; lia|].
destruct T4 as [Hni | Hlow].
- split; apply decLB_cell_apart; try exact Hni;
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address; lia.
- split; left; unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address; lia.
Qed.

(* ---- where *lenp lies: the caller's real stack (at or above sp), or a fake frame of the entry (below alloc_ceiling,
   apart from the decode block by AR's block / frame separation) ---- *)
Lemma decLB_lsite : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  4096 <= d_lenp d /\ d_lenp d + 8 <= 2 ^ 47 /\
  (forall a, d_lenp d <= a < d_lenp d + 8 -> (d_sp d <= a \/ a < alloc_ceiling) /\ ~ (q - HEAD <= a < q + d_n d)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (decL_lenp_range B d HE) as (L1 & L2 & _).
pose proof (decLB_sp d HE) as (S1 & S2 & S3).
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & _).
destruct HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
split; [exact L1|]. split; [exact L2|].
intros a Ha.
destruct HPL as [(HFP & Hsplp & _) | (HFP & Hot & (cid & pos & Hinf & Hr) & _)].
- unfold d_sp in *. split; [left; lia|]. unfold HEAD. lia.
- pose proof HH as (HJ & HARU & _). destruct HARU as (HARc & _ & _).
  unfold dec_J in HJ. destruct HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
  assert (Hinf' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; exact Hinf).
  pose proof (proj1 (proj1 (proj1 HPRE))) as HAR0.
  destruct (al_layout _ _ LAWS (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d)) (d_md d) lyc HAR0 Hly)
    as (_ & Hfa & _).
  pose proof (sep_block_frame tfibsegs B LAWS lyc Sc Wc (unpoison Uc memc) mdc (q - HEAD) (d_n d + HEAD) cid pos
    HARc Hin Hinf') as Hsep.
  rewrite Hfa, RQ in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
  pose proof (Hr a Ha) as Hra. unfold in_zr, frame_rng in Hra. cbn [fst snd] in Hra.
  pose proof (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos HAR0 Hinf) as (F1 & F2 & _).
  split; [right; lia | unfold HEAD in *; lia].
Qed.

(* ---- the transport of decL_memf: equal aview everywhere but the stack below sp at or above alloc_ceiling and the
   decode block's unwritten tail [q + |six_bytes six|, q + d_n) ---- *)
Lemma decLB_tr : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k m1 m2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  decL_memf B d q six Wc lyc Sc m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < d_sp d) ->
     ~ (q + Z.of_nat (length (WriterSpec.six_bytes six)) <= a < q + d_n d) ->
     aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a) ->
  decL_memf B d q six Wc lyc Sc m2.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k m1 m2 HE HH HM HA.
pose proof asan_consts as (C1 & _).
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & Happq & NIq & NIN).
pose proof (decLB_sp d HE) as (S1 & S2 & S3).
destruct (decLB_lsite d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (L1 & L2 & LS).
pose proof (decLB_tsite d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as TS.
unfold HEAD in Hq, Happq, NIq, LS, TS.
pose proof HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & Hi & _ & Hlsix & _).
assert (HNB : Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d)
  by (unfold d_n; apply decLB_nbytes; lia).
pose proof HE as (_ & _ & _ & _ & _ & Hcs & _). pose proof Hcs as (_ & Ht4096 & Htc & _).
set (L := Z.of_nat (length (WriterSpec.six_bytes six))) in *.
assert (A1 : forall a, 0 <= a < alloc_ceiling -> ~ (q + L <= a < q + d_n d) ->
  aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a) by (intros a Ha Hb; apply HA; lia).
assert (A2 : forall a, d_sp d <= a < 2 ^ 64 -> aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a)
  by (intros a Ha; apply HA; lia).
assert (ASH : forall a, SHADOW_OFF <= a < kHighMemBeg -> aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a).
{ intros a Ha. apply A1; unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, HEAD in *; lia. }
assert (AIMG : forall a, in_img tfibsegs a -> aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a).
{ intros a Hia. pose proof (fs_segs_img a Hia) as Hl. unfold FS_IMG_END in Hl.
  apply A1; [lia|]. intros X. apply (NIq a); [unfold HEAD; lia | exact Hia]. }
destruct HM as (Hrb1 & Hra1 & Hgl1 & Hkept1 & Hzb1).
split.
{ destruct Hrb1 as (Hin1 & H16 & Hn1 & Hv1). split; [exact Hin1|]. split; [exact H16|]. split; [exact Hn1|].
  apply (decLB_val_mem _ m1 m2 _ _ _); [|exact Hv1]. intros kk Hk. apply A1; unfold HEAD in *; lia. }
split.
{ apply (range_addressable_agree (aview tfibsegs (w_H Wc) m1) (aview tfibsegs (w_H Wc) m2) SHADOW_OFF q (d_n d));
    [|exact Hra1].
  intros x Hx. apply ASH. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg. lia. }
split.
{ unfold fs_glob, fs_glob_at in *. destruct Hgl1 as (V1 & V2 & V3 & V4 & R).
  assert (VB : forall g v, 0x10000 <= g -> g + 8 <= 0x5fd000 ->
    val_mem tfibsegs (mrestrict (w_H Wc) m1) g 8 v -> val_mem tfibsegs (mrestrict (w_H Wc) m2) g 8 v).
  { intros g v Hg1 Hg2 Hv. apply (decLB_val_mem _ m1 m2 _ _ _); [|exact Hv].
    intros kk Hk. apply AIMG. apply decLB_in_img. lia. }
  unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
  split; [apply VB; [lia | lia | exact V1]|]. split; [apply VB; [lia | lia | exact V2]|].
  split; [apply VB; [lia | lia | exact V3]|]. split; [apply VB; [lia | lia | exact V4]|]. exact R. }
split.
{ destruct Hkept1 as (Kv & Kw & Kc & Kr).
  split.
  { apply (decLB_val_mem _ m1 m2 _ _ _); [|exact Kv]. intros kk Hk.
    destruct (LS (d_lenp d + Z.of_nat kk) ltac:(lia)) as ([Hs | Hc] & Hnq); [apply A2; lia | apply A1; lia]. }
  split.
  { intros a Ha Hno. destruct (Kw a Ha Hno) as [E1 E2]. split.
    - rewrite <- E1. apply (mbyte_of_aview tfibsegs). apply A2. lia.
    - etransitivity; [exact E2|]. apply decLB_wr_eq; [lia | | apply A2; lia].
      intros X. pose proof (fs_segs_img a X) as Hl. unfold FS_IMG_END in Hl. lia. }
  split.
  { apply (decLB_cstr_agree Wc m1 m2 (d_text d) (d_tb d)); [| exact ASH | exact Kc].
    intros a Ha. pose proof (Z.mod_pos_bound (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hm.
    (* the word holding the NUL ends at or below alloc_ceiling, which is 4096-aligned (YM05.alloc_ceiling_value) *)
    pose proof (Z.div_mod (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hdm.
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as Hda.
    pose proof (proj2 YM05.alloc_ceiling_value) as Hac.
    destruct (TS a Ha) as (T1 & _). apply A1; [lia|]. unfold HEAD in *. lia. }
  intros a Hro Ho He. rewrite (AIMG a (decLB_ro_img a Hro)). exact (Kr a Hro Ho He). }
unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ q _ Hzb1). intros a Ha. fold L in Ha.
apply (mbyte_of_aview tfibsegs). apply A1; unfold HEAD in *; lia.
Qed.

(* (3) dec_head's memory conjuncts, and their transport over a change of the memory inside a stack window [lo, hi)
   below the entry sp (the loop's own frame, the runtime callee's stack) *)
Lemma decLB_memf : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k -> decL_memf B d q six Wc lyc Sc memc.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH.
destruct HH as (_ & _ & _ & _ & _ & _ & _ & Hrb & Hra & _ & Hgl & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & Hkept & Hzb & _).
exact (conj Hrb (conj Hra (conj Hgl (conj Hkept Hzb)))).
Qed.
Lemma decLB_keep : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 lo hi,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  decL_memf B d q six Wc lyc Sc memc1 -> alloc_ceiling <= lo -> hi <= d_sp d ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H Wc) memc2 a = aview tfibsegs (w_H Wc) memc1 a) ->
  decL_memf B d q six Wc lyc Sc memc2.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 lo hi HE HH HM Hlo Hhi HA.
apply (decLB_tr d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 HE HH HM).
intros a Ha H1 H2. apply HA; [exact Ha | lia].
Qed.
(* the same with one more decoded byte b stored at q + n (n the bytes decoded so far) *)
Lemma decLB_store : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 lo hi six' b,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  decL_memf B d q six Wc lyc Sc memc1 -> alloc_ceiling <= lo -> hi <= d_sp d ->
  Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> a <> q + Z.of_nat (length (WriterSpec.six_bytes six)) ->
     aview tfibsegs (w_H Wc) memc2 a = aview tfibsegs (w_H Wc) memc1 a) ->
  aview tfibsegs (w_H Wc) memc2 (q + Z.of_nat (length (WriterSpec.six_bytes six))) = Some b -> 0 <= b < 256 ->
  WriterSpec.six_bytes six' = WriterSpec.six_bytes six ++ [b] ->
  decL_memf B d q six' Wc lyc Sc memc2.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 lo hi six' b
  HE HH HM Hlo Hhi Hlen HA Hb Hbr Hsix.
assert (HM2 : decL_memf B d q six Wc lyc Sc memc2).
{ apply (decLB_tr d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 HE HH HM).
  intros a Ha H1 H2. apply HA; [exact Ha | lia | lia]. }
destruct HM2 as (R1 & R2 & R3 & R4 & R5).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
unfold zbytes_at in *. rewrite Hsix.
destruct (aview_byte tfibsegs (w_H Wc) memc2 _ b Hb) as (w & Ew & Ebw & _).
apply (garr8_app1 tfibsegs _ _ q _ b R5); [| exact Hbr | intros a _; reflexivity].
intros [|kk] Hk; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Ew. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. subst b. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* (4) memchr (g_b64, c, 65)'s premises on a memory that agrees with the cut's outside a stack window (FSH_Gen.v:474-481);
   b64_table = g_b64's 64 letters and its NUL (WriterSpec.v:62) *)
Lemma decLB_g64 : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 lo hi,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  alloc_ceiling <= lo -> hi <= d_sp d ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H Wc) memc1 a = aview tfibsegs (w_H Wc) memc a) ->
  rom_view tfibsegs Wc memc1 /\ zbytes_at tfibsegs Wc memc1 G_B64 WriterSpec.b64_table /\
  range_addressable (aview tfibsegs (w_H Wc) memc1) SHADOW_OFF G_B64 65 /\
  shadow_hull_vis (aview tfibsegs (w_H Wc) memc1) G_B64 65.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 lo hi HE HH Hlo Hhi HA.
pose proof asan_consts as (C1 & _).
pose proof HH as (_ & HARU & _).
pose proof HARU as (HARc & HUOKc & HUPOc).
pose proof (decLB_memf d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (_ & _ & _ & (_ & _ & _ & Kr) & _).
assert (A1 : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H Wc) memc1 a = aview tfibsegs (w_H Wc) memc a)
  by (intros a Ha; apply HA; lia).
assert (AU : forall a, in_img tfibsegs a ->
  aview tfibsegs (w_H Wc) memc1 a = aview tfibsegs (w_H Wc) (unpoison Uc memc) a).
{ intros a Hia. pose proof (fs_segs_img a Hia) as Hl. unfold FS_IMG_END in Hl.
  rewrite A1 by lia. symmetry. apply (decLB_aview_unp lyc Sc Uc Wc memc mdc a HARU); [lia | left; unfold SHADOW_OFF; lia]. }
assert (Kr' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) (unpoison Uc memc))).
{ intros a Hro Ho He. pose proof (decLB_ro_img a Hro) as Hia. pose proof (fs_segs_img a Hia) as Hl.
  unfold FS_IMG_END in Hl.
  rewrite (decLB_aview_unp lyc Sc Uc Wc memc mdc a HARU); [exact (Kr a Hro Ho He) | lia | left; unfold SHADOW_OFF; lia]. }
pose proof HIMG as (_ & HIM2).
destruct (HIM2 lyc Sc Wc (unpoison Uc memc) mdc HARc Kr') as (Hrom & _ & Hstrs & _).
assert (HinG : In (G_B64, map WriterSpec.b64c (map Z.of_nat (seq 0 64))) FS_RO_STRS)
  by (unfold FS_RO_STRS; repeat (first [left; reflexivity | right])).
pose proof (proj1 (Forall_forall _ _) Hstrs _ HinG) as (Hcs & _). cbn [fst snd] in Hcs.
assert (HL : length (map WriterSpec.b64c (map Z.of_nat (seq 0 64))) = 64%nat) by reflexivity.
destruct Hcs as ((Hg & _) & _ & _ & _ & _ & Hra & Hhv & _).
rewrite HL in Hra, Hhv. change (Z.of_nat 64 + 1) with 65 in Hra, Hhv.
split.
{ intros a Ha. pose proof Ha as (sg & Hsg & _ & Hr).
  assert (Hia : in_img tfibsegs a) by (exists sg; split; [exact Hsg | exact Hr]).
  rewrite (AU a Hia). exact (Hrom a Ha). }
split.
{ unfold zbytes_at, WriterSpec.b64_table. apply (garr8_frame tfibsegs _ _ G_B64 _ Hg). intros a Ha.
  rewrite length_app, HL in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). apply AU. apply decLB_in_img. unfold G_B64 in *. lia. }
split.
{ apply (range_addressable_agree (aview tfibsegs (w_H Wc) (unpoison Uc memc)) (aview tfibsegs (w_H Wc) memc1)
    SHADOW_OFF G_B64 65); [|exact Hra].
  intros x Hx. rewrite A1 by (unfold shadow_of_addr, SHADOW_OFF, G_B64 in *; lia).
  symmetry. apply (aview_unpoison_out tfibsegs). rewrite wz by (unfold shadow_of_addr, SHADOW_OFF, G_B64 in *; lia).
  apply (decLB_ush lyc Sc Uc Wc memc mdc x HARc HUOKc); [unfold G_B64 in *; lia|]. left.
  apply decLB_in_img. unfold G_B64 in *. lia. }
intros s Hs.
assert (Hs0 : 0 <= s < alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF, G_B64 in *; lia).
rewrite A1 by exact Hs0.
destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 s))) eqn:EU.
- rewrite wz in EU by lia. rewrite (HUPOc s EU). discriminate.
- rewrite <- (aview_unpoison_out tfibsegs (w_H Wc) Uc memc s EU). exact (Hhv s Hs).
Qed.

(* (5) *lenp on the caller's real stack (decode_spec's placement): its 8 bytes addressable (stack shadow is 0: AR's
   zero_shadow_ranges, as FSW_put.v:177-211), writable, out of the shadow band, apart from the frame *)
Lemma decLB_lenp : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  d_FP d = FS_PSTAT_FP ->
  d_sp d <= d_lenp d /\ d_lenp d + 8 <= d_ot d /\ d_lenp d mod 8 = 0 /\ 2 ^ 46 <= d_lenp d /\
  kHighMemBeg <= d_lenp d /\ d_lenp d + 8 <= 2 ^ 47 /\
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF (d_lenp d) 8 /\
  (forall a, d_lenp d <= a < d_lenp d + 8 -> writable_at tfibsegs (mrestrict (w_H Wc) memc) a).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFP.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & _).
pose proof (decLB_sp d HE) as (S1 & S2 & S3).
destruct HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hl8 & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
destruct HPL as [(_ & Hsplp & Hlpot & _ & Hottop & _) | (HFP' & _)].
2:{ exfalso. rewrite HFP in HFP'. apply (f_equal (@length (Z * Z))) in HFP'. rewrite length_app in HFP'.
    cbn [length] in HFP'. lia. }
pose proof (proj1 HPRE) as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop2).
unfold d_sp in *.
pose proof HH as (HJ & HARU & _).
pose proof HARU as (HARc & HUOKc & _).
unfold dec_J, d_STKJ in HJ.
destruct HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
unfold d_sp in Hpresc.
split; [exact Hsplp|]. split; [exact Hlpot|]. split; [exact Hl8|]. split; [lia|].
split; [unfold kHighMemBeg; lia|]. split; [lia|].
split.
{ assert (HLO : layout_ok lyc) by exact (am_layout _ _ _ _ (proj1 HARc)).
  pose proof (lo_top lyc HLO) as LTOP.
  assert (Hlo8 : ly_stk_lo lyc mod 8 = 0).
  { destruct LTOP as (_ & _ & _ & _ & L5 & _). unfold page_aligned in L5.
    apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
      [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L5]]. }
  assert (Hhi8 : ly_stk_hi lyc mod 8 = 0).
  { destruct LTOP as (_ & _ & _ & _ & _ & L6 & _). unfold page_aligned in L6.
    apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
      [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L6]]. }
  assert (HZS : zero_shadow (aview tfibsegs (w_H Wc) (unpoison Uc memc)) SHADOW_OFF
                  (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc)).
  { exact (al_zshadow _ _ LAWS lyc Sc Wc (unpoison Uc memc) mdc
             (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HARc (or_introl eq_refl)). }
  assert (HRAU : range_addressable (aview tfibsegs (w_H Wc) (unpoison Uc memc)) SHADOW_OFF (d_lenp d) 8).
  { eapply range_addressable_sub;
      [ apply (zero_shadow_range (aview tfibsegs (w_H Wc) (unpoison Uc memc)) SHADOW_OFF
                 (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc) Hlo8
                 ltac:(rewrite Zminus_mod, Hlo8, Hhi8; reflexivity) HZS)
      | lia | lia]. }
  eapply range_addressable_agree; [|exact HRAU].
  intros x Hx. apply aview_at. symmetry. apply unpoison_out.
  rewrite (wz (shadow_of_addr SHADOW_OFF x)) by (unfold shadow_of_addr, SHADOW_OFF; lia).
  apply (decLB_ush lyc Sc Uc Wc memc mdc x HARc HUOKc); [lia | right; lia]. }
intros a Ha.
apply (apresent_writable tfibsegs).
apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold kHighMemBeg; lia|].
apply Hpresc. lia.
Qed.
End L3.
