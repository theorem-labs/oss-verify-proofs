(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Record asink_img_laws {SK : YI16.sink_head} (segs : list Segment) (B : asyms) (K : asink_syms) : Prop := mkAIL {
ail_head : ak_ofl_head K = AOFL_HEAD;
ail_env : forall a, aenv_addr K a -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
ail_env_off : forall a, aenv_addr K a -> AOFL_HEAD <= a < AOFL_HEAD + 8 \/ ~ (AOFL_HEAD <= a < AOFL_HEAD + 8);
ail_env_static : forall a, a = ak_threaded K \/ a = ak_need_locks K \/ (ak_ofl_lock K <= a < ak_ofl_lock K + 4) \/
(ak_path K <= a < ak_path K + 13) \/ (ak_mode K <= a < ak_mode K + 3) \/ (ak_rwa K <= a < ak_rwa K + 4) \/
(ak_trailer K <= a < ak_trailer K + 2) \/ (ak_canary K <= a < ak_canary K + 8) -> ~ (AOFL_HEAD <= a < AOFL_HEAD + 8);
ail_can_got : forall ly, In (z8 (ANum (ak_can_got K)) (ak_canary K)) (as_const B ly);
ail_meta : forall a, ak_meta_mem K <= a < ak_meta_mem K + 8 ->
in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\ a < AOFL_HEAD;
ail_meta_ptr : forall ly, In (z8 (ANum (ak_meta_ptr K)) (ak_meta_mem K)) (as_const B ly);
ail_errno_img : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a;
ail_icells : forall ly c, In c (ak_icells K) -> In (z8 (ANum (fst c)) (snd c)) (as_const B ly)
}.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section J.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws segs B K.
Local Notation ajournal := (ajournal segs B).
Local Notation rd W mem := (mrestrict (w_H W) mem).
Lemma mbyte_kept_of_aview : forall (W W' : world segs) mem mem' a,
aview segs (w_H W') mem' a = aview segs (w_H W) mem a ->
mbyte segs (rd W' mem') a = mbyte segs (rd W mem) a.
Proof. intros W W' mem mem' a E. exact (mbyte_of_aview segs _ _ _ _ a E). Qed.
Lemma aenv_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k a,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> aenv_addr K a -> fp_spares FP a ->
mbyte segs (rd W' mem') a = mbyte segs (rd W mem) a.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k a HJ Ha Hsp.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He). apply mbyte_kept_of_aview. exact (F3 a Hi Hns He Hsp).
Qed.
Lemma asink_at_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k f Sg,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP ->
In (f, FILE_BLOCK) (ablocks B ly S) -> In (f, FILE_BLOCK) (ablocks B ly' S') ->
(forall i, 0 <= i < FILE_BLOCK -> ~ inFP FP (f + i)) ->
asink_at segs K (rd W mem) md f Sg -> asink_at segs K (rd W' mem') md' f Sg.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k f Sg HJ Hcl Hb Hb' HnF HA.
pose proof HJ as (_ & _ & _ & _ & Hos & _ & _ & _ & _ & F2 & F3 & _).
destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & Eproc & Eio).
apply (asink_at_model segs K (rd W' mem') md md' f Sg).
- unfold m_fs. rewrite Efsys. reflexivity.
- unfold m_fds. rewrite Efd. reflexivity.
- apply (asink_at_frame segs K (rd W mem) (rd W' mem')); [|exact HA].
intros a [Hblk | Henv].
+ apply mbyte_kept_of_aview. replace a with (f + (a - f)) by lia.
assert (HFB : req_size FILE_BLOCK = FILE_BLOCK) by reflexivity.
apply (F2 f FILE_BLOCK (a - f) Hb Hb'); [rewrite HFB; lia | apply HnF; lia].
+ eapply aenv_kept; [exact HJ | exact Henv | apply fp_spares_closed; exact Hcl].
Qed.
Lemma asink_none_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP ->
asink_none segs K (rd W mem) md -> asink_none segs K (rd W' mem') md'.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hcl (Henv & Hhead & Hn).
pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & Eproc & Eio).
assert (FR : forall a, aenv_addr K a -> mbyte segs (rd W' mem') a = mbyte segs (rd W mem) a).
{ intros a Ha. eapply aenv_kept; [exact HJ | exact Ha | apply fp_spares_closed; exact Hcl]. }
split; [exact (astdio_env_frame segs K _ _ FR Henv)|]. split.
- eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply FR. unfold aenv_addr, ak_ofl_head in *. cbn in Hx. lia.
- unfold m_fds in *. rewrite Efd. exact Hn.
Qed.
Lemma astdio_env_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
astdio_env segs K (rd W mem) -> astdio_env segs K (rd W' mem').
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (cv & Hcv & H8)).
assert (FR : forall a, a = ak_threaded K \/ a = ak_need_locks K \/ (ak_ofl_lock K <= a < ak_ofl_lock K + 4) \/
(ak_path K <= a < ak_path K + 13) \/ (ak_mode K <= a < ak_mode K + 3) \/ (ak_rwa K <= a < ak_rwa K + 4) \/
(ak_trailer K <= a < ak_trailer K + 2) \/ (ak_canary K <= a < ak_canary K + 8) -> mbyte segs (rd W' mem') a = mbyte segs (rd W mem) a).
{ intros a Ha. eapply aenv_kept; [exact HJ | unfold aenv_addr; lia | apply fp_spares_off; exact (ail_env_static _ _ _ AIL a Ha)]. }
unfold astdio_env.
split; [eapply val_mem_frame; [|exact H1]; intros x Hx; apply FR; cbn in Hx; lia|].
split; [eapply val_mem_frame; [|exact H2]; intros x Hx; apply FR; cbn in Hx; lia|].
split; [eapply val_mem_frame; [|exact H3]; intros x Hx; apply FR; cbn in Hx; lia|].
split; [eapply garr8_frame; [exact H4|]; intros x Hx; apply FR; cbn in Hx; lia|].
split; [eapply garr8_frame; [exact H5|]; intros x Hx; apply FR; cbn in Hx; lia|].
split; [eapply garr8_frame; [exact H6|]; intros x Hx; apply FR; cbn in Hx; lia|].
split; [eapply garr8_frame; [exact H7|]; intros x Hx; apply FR; cbn in Hx; lia|].
exists cv. split; [exact Hcv|]. eapply val_mem_frame; [|exact H8]; intros x Hx; apply FR; cbn in Hx; lia.
Qed.
Lemma acan_got_of_AR : forall ly S W mem md,
AR segs B ly S W mem md -> val_mem segs (rd W mem) (ak_can_got K) 8 (ak_canary K).
Proof.
intros ly S W mem md HAR k Hk.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
pose proof (proj1 (Forall_forall _ _) HC _ (ail_can_got _ _ _ AIL ly)) as Hc. unfold z8, c8, cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte segs (mrestrict (w_H W) mem) (ak_can_got K + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte (ak_canary K) 8 k) with (YG0f.le_byte (ak_canary K) 8 k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.
Lemma icell_of_AR : forall ly S W mem md a v,
AR segs B ly S W mem md -> In (a, v) (ak_icells K) -> 0 <= v < 2 ^ 64 -> val_mem segs (rd W mem) a 8 v.
Proof.
intros ly S W mem md a v HAR Hin Hv k Hk.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
pose proof (proj1 (Forall_forall _ _) HC _ (ail_icells _ _ _ AIL ly (a, v) Hin)) as Hc. unfold z8, c8, cell_holds in Hc. cbn [fst snd c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte segs (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.
Definition ameta_inv (ly : alayout) (m : word -> option byte) (M : Z) : Prop :=
In (M, AMETA_SIZE) (ly_extra ly) /\ (forall a, in_img segs a -> a < M) /\ ameta_ok segs K m M.
Lemma ameta_ptr_of_AR : forall ly S W mem md,
AR segs B ly S W mem md -> val_mem segs (rd W mem) (ak_meta_ptr K) 8 (ak_meta_mem K).
Proof.
intros ly S W mem md HAR k Hk.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
pose proof (proj1 (Forall_forall _ _) HC _ (ail_meta_ptr _ _ _ AIL ly)) as Hc. unfold z8, c8, cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte segs (mrestrict (w_H W) mem) (ak_meta_ptr K + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte (ak_meta_mem K) 8 k) with (YG0f.le_byte (ak_meta_mem K) 8 k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.
Lemma ameta_inv_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
ameta_inv ly (rd W mem) M -> ameta_inv ly' (rd W' mem') M.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M HJ (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ).
pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (HX' : In (M, AMETA_SIZE) (ly_extra ly')) by (rewrite Eextra; exact HX).
split; [exact HX'|]. split; [exact Himg|]. split; [exact (ameta_ptr_of_AR _ _ _ _ _ HAR')|]. split.
- eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply mbyte_kept_of_aview.
destruct (ail_meta _ _ _ AIL x ltac:(lia)) as (Hi & Hns & He & Hlt). apply (F3 x Hi Hns He). apply fp_spares_below. exact Hlt.
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
intros a Ha. rewrite <- (HZ a Ha). apply mbyte_kept_of_aview. apply F5.
+ apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
+ intros He. pose proof (ail_errno_img _ _ _ AIL a He) as Hi.
destruct (AR_extra_law_ok segs B ly' S' W' mem' md' a HAR'
ltac:(apply Exists_exists; exists (M, AMETA_SIZE); split; [exact HX' | unfold in_zr; cbn [fst snd]; lia])) as (_ & _ & _ & _ & Hni & _).
exact (Hni Hi).
Qed.
Definition AFWRITE_STK : Z := 6352.
Definition afwrite_spec (pc : Z) : Prop :=
forall W ly S regs mem md ch (p n f : Z) (Sg bs : list Z),
afn_pre segs B AFWRITE_STK ly S W regs mem md ch ->
getr regs 10 = w64 p -> getr regs 11 = w64 1 -> getr regs 12 = w64 n -> getr regs 13 = w64 f ->
In (f, FILE_BLOCK) (ablocks B ly S) -> asink_at segs K (rd W mem) md f Sg ->
garr8 segs (rd W mem) p bs -> n = Z.of_nat (length bs) -> 1 <= n <= 2 ^ 30 ->
Z.of_nat (length Sg) + n <= SINK_MAX ->
(p + n <= f \/ f + FILE_BLOCK <= p) -> (p + n <= spZ regs - AFWRITE_STK \/ spZ regs <= p) -> 0 <= p -> amem_range p n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n -> shadow_hull_vis (aview segs (w_H W) mem) p n ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal AFWRITE_STK (spZ regs) (asink_fp f) ly S W mem md [] ly S W' mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 n /\
asink_at segs K (rd W' mem') md' f (Sg ++ bs)).
Definition arodata_okS (rlo rhi : Z) (rd : reader) : Prop :=
forall a, ((exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (rlo <= a < rhi)) ->
~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Definition AFCLOSE_STK : Z := 16528.
Definition afclose_spec (pc ra1 ra2 rlo rhi : Z) : Prop :=
forall W ly S regs mem md ch (f M : Z) (Sg : list Z) (rest : list (Z * Z)),
afn_pre segs B AFCLOSE_STK ly S W regs mem md ch ->
getr regs 10 = w64 f ->
Permutation (ablocks B ly S) ((f, FILE_BLOCK) :: rest) ->
asink_at segs K (rd W mem) md f Sg ->
ameta_inv ly (rd W mem) M -> arodata_okS rlo rhi (aview segs (w_H W) mem) ->
st_nev S + 2 <= EV_MAX ->
In [pc_free_ra0 (as_code B); ra1] (as_universe B) -> In [pc_free_ra0 (as_code B); ra2] (as_universe B) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal AFCLOSE_STK (spZ regs) (asink_fp f) ly S W mem md [] ly' S' W' mem' md' 2 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') rest /\ frames S' = frames S /\
asink_none segs K (rd W' mem') md' /\ Fs.fs_lookup (m_fs md') sink_path = Some (bytes Sg)).
Definition AFOPEN_STK : Z := 18624.
Definition afopen_spec (pc ra rlo rhi : Z) : Prop :=
forall W ly S regs mem md ch (M : Z),
afn_pre segs B AFOPEN_STK ly S W regs mem md ch ->
getr regs 10 = w64 (ak_path K) -> getr regs 11 = w64 (ak_mode K) ->
asink_none segs K (rd W mem) md ->
ameta_inv ly (rd W mem) M -> arodata_okS rlo rhi (aview segs (w_H W) mem) ->
st_nev S + 1 <= EV_MAX -> blocks_bytes S + FILE_BLOCK <= LIVE_MAX ->
In [pc_malloc_ra0 (as_code B); ra] (as_universe B) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' (res k : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal AFOPEN_STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 res /\ frames S' = frames S /\
((res = 0 /\ k = 0 /\ ablocks B ly' S' = ablocks B ly S /\ asink_none segs K (rd W' mem') md' /\
m_fds md' = m_fds md /\ m_fs md' = m_fs md /\
(exists e, 1 <= e <= 4095 /\ val_mem segs (rd W' mem') (as_errno B) 4 e))
\/
(4096 <= res /\ k = 1 /\ ablocks B ly' S' = ablocks B ly S ++ [(res, FILE_BLOCK)] /\
asink_at segs K (rd W' mem') md' res [] /\ Fs.fs_lookup (m_fs md') sink_path = Some []))).
Definition AUNLINK_STK : Z := 32.
Definition aunlink_spec (pc : Z) : Prop :=
forall W ly S regs mem md ch,
afn_pre segs B AUNLINK_STK ly S W regs mem md ch ->
getr regs 10 = w64 (ak_path K) ->
asink_none segs K (rd W mem) md ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => exists regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal AUNLINK_STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly S W' mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 res /\
asink_none segs K (rd W' mem') md' /\ m_fds md' = m_fds md /\
((res = 0 /\ m_fs md' = fs_remove (m_fs md) sink_path) \/
(exists e, 1 <= e <= 4095 /\ res = 2 ^ 64 - 1 /\ m_fs md' = m_fs md /\ val_mem segs (rd W' mem') (as_errno B) 4 e))).
End J.
End d.
