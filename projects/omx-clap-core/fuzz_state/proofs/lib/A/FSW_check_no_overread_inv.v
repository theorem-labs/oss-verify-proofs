(* check_no_overread 0x811c8 (fs.c), fs.asan: the two machine-level boundaries that cut the rest of the walk into
   three independent segments (owner of this file: a Theorem Labs lane).
   - INV_D1: the machine at the first preset_base64_decode call (pc A_preset_base64_decode, ra 0x8139c), after
     __wrap_malloc, __asan_memcpy, __asan_memset, the inline shadow check 0x81358-0x81364, the store 0x81374 and the
     lifetime-start stores 0x81378-0x8138c;
   - INV_F1: the machine at the first fuzz_free call (pc A_fuzz_free, ra 0x81424), after the three decodes, the
     branches 0x813c8 / 0x813d4 / 0x813d8 / 0x813e4 / 0x813e8 / 0x81540-0x81544, both bcmp calls and 0x81404.
   The segments (each a Prop below, proved in its own file):
   - segM (_top.v, a Theorem Labs lane):  cno_at A_preset_base64_decode INV_D1 -> cno_from B ss_M INV_M;
   - segD (cno_segD_T):        cno_at A_fuzz_free INV_F1 -> cno_at A_preset_base64_decode INV_D1;
   - segF (cno_segF_T):        cno_from B cno_ss_R (INV_R B) -> cno_at A_fuzz_free INV_F1.
   A boundary is a machine (regs, mem at the callee's entry pc), not a symbolic state: the segment after it starts
   with the call step (cno_call_dec_T / cno_call_ffree_T, from cno_site) and rebuilds the resume state with
   FSW_check_no_overread_top.v cno_resume; cno_mframe carries every byte cno_resume's chunks read (the thirteen saved
   words, the frame's flag word, the slots 0x10 / 0x18). *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret
FSW_rres FSW_frame FSW_strkit FSW_rd FSH_Fn_cno FSH_Fn_alloc FSW_check_no_overread_tbl FSW_check_no_overread.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer ACem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the chain's generic steps (moved from FSW_check_no_overread_top.v so the segment files share
   them): reading a call-site state, the resume after a call (cno_resume), the runs' kept bytes ================= *)
Ltac cno_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* lia on the arithmetic hypotheses only (some kit hypotheses stop lia's preprocessing; FSW_entry_s8.v fe8_lia) *)
Ltac cno_lia :=
  repeat match goal with H : ?T |- _ =>
    match type of T with Prop =>
      lazymatch T with
      | _ <= _ => fail | _ < _ => fail | @eq Z _ _ => fail
      | _ /\ _ => fail | _ \/ _ => fail
      | _ => clear H
      end
    end
  end; lia.

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the registers every boundary has: sp = s1 = sp1, s0 = sp0, s2 = the frame's shadow, s3 = the frame, gp / tp *)
Definition cno_core (cx : cnocx) (E : env) : Prop :=
  ew E 2 = w64 (cno_sp1 cx) /\ ew E 8 = w64 (cno_sp0 cx) /\ ew E 9 = w64 (cno_sp1 cx) /\
  ew E 18 = w64 (cno_SF cx) /\ ew E 19 = w64 (cno_F cx) /\
  ew E 3 = getr (c_regs cx) 3 /\ ew E 4 = getr (c_regs cx) 4.
(* the env of a boundary: the machine's registers, the context's extra atoms and the walk's blocks a / b / t *)
Definition cno_env (cx : cnocx) (regs : bvmap 5 word) (A Bp T : Z) : env :=
  Ereg regs (fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) A Bp T).

Lemma cno_E_env : forall cx regs A Bp T, cno_E cx (cno_env cx regs A Bp T).
Proof.
intros cx regs A Bp T. unfold cno_E, cno_env. split; [|split; [|split]].
- change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
- intros j Hj. change (33 + j)%nat with (32 + S j)%nat. rewrite ew_Ereg_extra.
  do 13 (destruct j as [|j]; [reflexivity|]). lia.
- change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. reflexivity.
- change 47%nat with (32 + 15)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* a chunk read under one env holds under another that gives its value the same word *)
Lemma cno_chunk_env : forall E E' m b o (w : N) e e',
  YP09.chunk_ok tfibsegs E m b (YP09.mkChunk o (CVal w e)) -> sv_denot E' e' = sv_denot E e ->
  YP09.chunk_ok tfibsegs E' m b (YP09.mkChunk o (CVal w e')).
Proof.
intros E E' m b o w e e' H He i Hi. destruct (H i Hi) as (x & H1 & H2). exists x. split; [|exact H2].
cbn [YP09.cbyte YP09.c_val YP09.c_off] in *. rewrite He. exact H1.
Qed.

(* the saved words of a state whose first region is the prologue's (cno_sv_chunks at s0 = sp0): the entry ra and
   s0 at sp0 - 8 / sp0 - 16, and the thirteen chunks under any env with the same extra atoms 33 .. 45 *)
Lemma cno_saved_of_st : forall cx E ss (W : world tfibsegs) ms,
  cno_E cx E -> bv_unsigned (ew E 8) = cno_sp0 cx ->
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (fs_ret_s0_region (-104) 0 cno_sv_chunks) ->
  rdword (aview tfibsegs (w_H W) (ms_mem ms)) (cno_sp0 cx - 8) = Some (raZ (c_regs cx)) /\
  rdword (aview tfibsegs (w_H W) (ms_mem ms)) (cno_sp0 cx - 16) = Some (s0Z (c_regs cx)) /\
  (forall E', (forall j, (j < 13)%nat -> ew E' (33 + j) = ew E (33 + j)) ->
     Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms)) (cno_sp0 cx)) cno_sv_chunks).
Proof.
intros cx E ss W ms HE E8 HS Hn.
pose proof (fsw_region_nth _ _ _ 0 _ HS Hn) as HR. cbn [ms_mem restrict] in HR.
destruct HE as (_ & HE & _).
split; [|split].
- replace (cno_sp0 cx - 8) with (cno_sp0 cx + -8) by lia.
  apply (ACem.rdword_of_val_mem tfibsegs); [|unfold raZ; apply u64_range].
  apply (fsw_field _ _ 8 _ _ _ _ _ _ (-8) 8%N (SOff 33 0) (raZ (c_regs cx)) HR E8 ltac:(cbn; tauto)).
  + pose proof (HE 0%nat ltac:(lia)) as X. cbn [Nat.add] in X. rewrite fsw_SOff0, X. cbn [nth cno_saved_regs]. unfold raZ. symmetry.
    apply Z_to_bv_bv_unsigned.
  + unfold raZ. apply u64_range.
  + cbn; lia.
- replace (cno_sp0 cx - 16) with (cno_sp0 cx + -16) by lia.
  apply (ACem.rdword_of_val_mem tfibsegs); [|unfold s0Z; apply u64_range].
  apply (fsw_field _ _ 8 _ _ _ _ _ _ (-16) 8%N (SOff 34 0) (s0Z (c_regs cx)) HR E8 ltac:(cbn; tauto)).
  + pose proof (HE 1%nat ltac:(lia)) as X. cbn [Nat.add] in X. rewrite fsw_SOff0, X. cbn [nth cno_saved_regs]. unfold s0Z. symmetry.
    apply Z_to_bv_bv_unsigned.
  + unfold s0Z. apply u64_range.
  + cbn; lia.
- intros E' HE'. destruct HR as (_ & _ & _ & Hcs).
  cbn [fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite E8 in Hcs.
  apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
  unfold cno_sv_chunks in Hc. cbn [seq map Z.of_nat Nat.add] in Hc.
  repeat (destruct Hc as [<- | Hc];
    [apply (cno_chunk_env _ _ _ _ _ _ _ _ Hck); rewrite !fsw_SOff0;
     match goal with |- ew E' ?n = ew E ?n =>
       let j := eval cbv in (n - 33)%nat in exact (HE' j ltac:(cbv; lia)) end |]).
  destruct Hc.
Qed.

(* the ledger cells, when a step keeps their bytes *)
Lemma cno_glob_ledger : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail HK (V1 & V2 & V3 & V4 & R).
assert (VK : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv k Hk. rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W') m m').
  - exact (Hv k Hk).
  - apply HK. apply (inFP_FS_PSTAT_FP g Hg). lia. }
split; [apply VK; [cbn; tauto | exact V1]|].
split; [apply VK; [cbn; tauto | exact V2]|].
split; [apply VK; [cbn; tauto | exact V3]|].
split; [apply VK; [cbn; tauto | exact V4] | exact R].
Qed.

(* d's text at a call: the entry's src_rd, kept by the journal (the block survives and is no static) and by the
   shadow (the block's bytes are addressable on the unpoisoned reading, and none of their shadow bytes is U's, as
   they were addressable at the entry) *)
Lemma cno_src_kept : forall cx k ly S (W : world tfibsegs) mem md,
  cno_base B cx -> cno_J B cx k ly S W (unpoison (c_U cx) mem) md -> ARU tfibsegs B ly S (c_U cx) W mem md ->
  src_rd tfibsegs W mem (c_d cx) (c_db cx) /\
  (0 < cno_n cx -> exists b m, In (b, m) (ablocks B ly S) /\ b <= c_d cx /\ c_d cx + cno_n cx <= b + m).
Proof.
intros cx k ly S W mem md Hb HJ HARU.
pose proof Hb as (HPRE & _ & _ & _ & _ & _ & Hsrc & _ & Hblk & _).
pose proof (proj1 HPRE) as HAPU. pose proof HAPU as (HAP & OK0 & PO0).
pose proof (fsw_ARU B _ _ _ _ _ _ _ _ _ HAPU) as HARU0.
pose proof (ARU_AR tfibsegs B ly S (c_U cx) W mem md HARU) as HAR.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU0) as HAR0.
pose proof HARU as (_ & _ & PO).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & _ & Hgone & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hsrc as (Hz & H4096 & Hceil & Ham & Hra & Hhv).
assert (Hlive : 0 < cno_n cx -> exists b m, In (b, m) (ablocks B ly S) /\
  In (b, m) (ablocks B (c_ly cx) (c_S cx)) /\ b <= c_d cx /\ c_d cx + cno_n cx <= b + m).
{ intros Hn0. destruct (Hblk Hn0) as (b & m & Hin & H1 & H2). exists b, m.
  split; [|split; [exact Hin | split; [exact H1 | exact H2]]].
  assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
  destruct (in_dec Hdec (b, m) (ablocks B ly S)) as [Hy | Hy]; [exact Hy|]. exfalso.
  destruct (fsw_ablock_low B _ _ _ _ _ b m HAR0 Hin) as (L1 & L2 & L3).
  pose proof (Hgone b m 0 Hin Hy ltac:(lia)) as Hfp. rewrite Z.add_0_r in Hfp.
  destruct (fsw_ablock_off_img B _ _ _ _ _ b m HAR0 Hin) as [Ho | Ho].
  - destruct Hfp as (r & Hr & Hr2). unfold FS_PSTAT_FP in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hr2; lia.
  - destruct Hfp as (r & Hr & Hr2). unfold FS_PSTAT_FP in Hr. unfold FS_IMG_END in Ho.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hr2; lia. }
split; [|intros Hn0; destruct (Hlive Hn0) as (b & m & H1 & _ & H3 & H4); exists b, m; auto].
(* a byte of d's text reads the same now as at the entry *)
assert (KB : forall j, 0 <= j < cno_n cx ->
  aview tfibsegs (w_H W) mem (c_d cx + j) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_d cx + j)).
{ intros j Hj. destruct (Hlive ltac:(lia)) as (b & m & Hin & Hin0 & H1 & H2).
  destruct (fsw_ablock_low B _ _ _ _ _ b m HAR Hin) as (L1 & L2 & L3).
  replace (c_d cx + j) with (b + (c_d cx + j - b)) by lia.
  pose proof (req_size_pos m ltac:(lia)) as Hrq.
  rewrite <- (cno_blk_unp B ly S (c_U cx) W mem md b m (c_d cx + j - b) HARU Hin ltac:(lia)).
  rewrite <- (cno_blk_unp B _ _ _ _ _ _ b m (c_d cx + j - b) HARU0 Hin0 ltac:(lia)).
  apply (F2 b m (c_d cx + j - b) Hin0 Hin ltac:(lia)). intros Hfp.
  destruct (fsw_ablock_off_img B _ _ _ _ _ b m HAR0 Hin0) as [Ho | Ho];
    destruct Hfp as (r & Hr & Hr2); unfold FS_PSTAT_FP in Hr; unfold FS_IMG_END in Ho;
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hr2; lia. }
split; [|split; [exact H4096 | split; [exact Hceil | split; [exact Ham | split]]]].
- intros j Hj. destruct (Hz j Hj) as (Hv & Hr8). split; [|exact Hr8].
  intros q Hq. assert (q = 0%nat) as -> by lia.
  rewrite (mbyte_of_aview tfibsegs (w_H (c_W cx)) (w_H W) (c_mem cx) mem); [exact (Hv 0%nat Hq)|].
  replace (c_d cx + Z.of_nat j + Z.of_nat 0) with (c_d cx + Z.of_nat j) by lia.
  apply KB. unfold cno_n. lia.
- intros x Hx. assert (Hn0 : 0 < cno_n cx) by (unfold cno_n; lia).
  destruct (Hlive Hn0) as (b & m & Hin & Hin0 & H1 & H2).
  destruct (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison (c_U cx) mem) md b m (c_d cx) (cno_n cx)
    HAR Hin H1 ltac:(pose proof (req_size_pos m); destruct (fsw_ablock_low B _ _ _ _ _ b m HAR Hin); lia) x Hx)
    as (s & Hs & Hok).
  exists s. split; [|exact Hok].
  assert (Hush : in_ush (c_U cx) (shadow_addr x) = false)
    by exact (ush_off_addressable (c_U cx) (c_W cx) (c_mem cx) (c_d cx) (cno_n cx) x PO0 Hra Hx).
  change (shadow_addr x) with (shadow_of_addr SHADOW_OFF x) in Hush.
  assert (Hsr : 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64).
  { destruct (fsw_ablock_low B _ _ _ _ _ b m HAR Hin) as (L1 & L2 & L3). pose proof (req_size_pos m ltac:(lia)).
    unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
  rewrite <- (aview_unpoison_sh (c_U cx) W mem (shadow_of_addr SHADOW_OFF x) Hsr Hush).
  exact Hs.
- intros Hn0. destruct (Hlive Hn0) as (b & m & Hin & Hin0 & H1 & H2).
  pose proof (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (unpoison (c_U cx) mem) md b m (c_d cx) (cno_n cx)
    HAR Hin H1 ltac:(pose proof (req_size_pos m); destruct (fsw_ablock_low B _ _ _ _ _ b m HAR Hin); lia) Hn0) as Hv.
  intros s Hs. exact (aview_unpoison_vis (c_U cx) W mem s PO (Hv s Hs)).
Qed.

(* the machine at a call of the walk, read off the call-site symbolic state: cno_site *)
Lemma cno_site_of : forall cx E ss (W : world tfibsegs) ms k ly S U md r,
  cno_E cx E -> bv_unsigned (ew E 8) = cno_sp0 cx ->
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (fs_ret_s0_region (-104) 0 cno_sv_chunks) ->
  cno_J B cx k ly S W (unpoison U (ms_mem ms)) md -> ARU tfibsegs B ly S U W (ms_mem ms) md ->
  FSupoisonU.fs_heads B ly S U ->
  getr (ms_regs ms) 2 = w64 (cno_sp1 cx) -> getr (ms_regs ms) 8 = w64 (cno_sp0 cx) ->
  getr (ms_regs ms) 3 = getr (c_regs cx) 3 -> getr (ms_regs ms) 4 = getr (c_regs cx) 4 ->
  getr (ms_regs ms) 1 = w64 r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  cno_site B cx k ly S U W (ms_regs ms) (ms_mem ms) md.
Proof.
intros cx E ss W ms k ly S U md r HE E8 HS Hn HJ HARU Hh R2 R8 R3 R4 R1 Hr Hr2.
destruct (cno_saved_of_st cx E ss W ms HE E8 HS Hn) as (H8 & H16 & _).
split; [exact HJ|]. split; [exact HARU|]. split; [exact Hh|].
split; [exact R2|]. split; [exact R8|]. split; [exact R3|]. split; [exact R4|].
split; [rewrite R1; apply ret_ok_even; unfold w64; rewrite unsigned_lit_small by lia; exact Hr2|].
split; [unfold raZ; rewrite R1; unfold w64; rewrite unsigned_lit_small by lia; lia|].
split; [exact H8 | exact H16].
Qed.

(* the machine back at the return address of a call of the walk, with the symbolic resume state rebuilt
   (cno_after): the saved words read at the call, the frame and slot chunks kept by cno_ret's zone *)
Lemma cno_resume : forall cx k ly S U (W : world tfibsegs) regs mem md kc U' (Kp : Z -> Prop)
  (P : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c' xs csF cssl,
  cno_base B cx -> cno_site B cx k ly S U W regs mem md ->
  cno_ret B cx k ly S regs mem W kc U' Kp P W' c' ->
  getr regs 9 = w64 (cno_sp1 cx) -> getr regs 18 = w64 (cno_SF cx) -> getr regs 19 = w64 (cno_F cx) ->
  (forall a, cno_sp0 cx - 104 <= a < cno_sp0 cx -> ~ Kp a) ->
  regions_wf (fss_ret_s0_regs (-104) 0 cno_sv_chunks [cno_fr_region 19 csF; cno_sh_region 18; cno_sl_region cssl])
    = true ->
  (forall regs', Forall (YP09.chunk_ok tfibsegs (Ereg regs' xs) (mrestrict (w_H W) mem) (cno_sp0 cx)) cno_sv_chunks) ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 128 /\
    forall i, 0 <= i < YP09.c_len c -> ~ Kp (cno_F cx + YP09.c_off c + i)) csF ->
  Forall (fun c => 16 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 56 /\
    forall i, 0 <= i < YP09.c_len c -> ~ Kp (cno_sp1 cx + YP09.c_off c + i)) cssl ->
  (forall regs', aregs_preserved regs regs' ->
     Forall (YP09.chunk_ok tfibsegs (Ereg regs' xs) (mrestrict (w_H W) mem) (cno_F cx)) csF) ->
  (forall regs', aregs_preserved regs regs' ->
     Forall (YP09.chunk_ok tfibsegs (Ereg regs' xs) (mrestrict (w_H W) mem) (cno_sp1 cx)) cssl) ->
  exists ly' S' regs' mem' md',
    c' = mkCfg (mkst regs' (Z_to_bv 64 (raZ regs)) mem' (seg_rom tfibsegs)) md' /\
    cno_J B cx (k + kc) ly' S' W' (unpoison U' mem') md' /\ ARU tfibsegs B ly' S' U' W' mem' md' /\
    FSupoisonU.fs_heads B ly' S' U' /\ aregs_preserved regs regs' /\
    (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
       ~ Kp (p + i) -> aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) mem (p + i)) /\
    (forall a, cno_zone cx a -> ~ Kp a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
    P ly' S' W' regs' mem' md' /\
    st_ok tfibsegs (Ereg regs' xs) (cno_ss (raZ regs) 19 18 csF cssl)
      (restrict (w_H W') (mkst regs' (Z_to_bv 64 (raZ regs)) mem' (seg_rom tfibsegs))).
Proof.
intros cx k ly S U W regs mem md kc U' Kp P W' c' xs csF cssl Hb Hs Hret R9 R18 R19 HKs Hwf Hsv HcsFb Hcsslb
  HcsF Hcssl.
destruct Hret as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HZ & HBK & HPP).
pose proof Hs as (HJ & HARU & Hh & R2 & R8 & R3 & R4 & Hra & Hra4 & H8 & H16).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
pose proof HJ' as (_ & Hly' & _ & _ & _ & Hfrs' & _).
assert (Hin' : In (1, c_fpos cx) (frames S')) by (rewrite Hfrs'; left; reflexivity).
assert (EF' : ly_F ly' = ly_F (c_ly cx)) by (destruct Hly' as (_ & _ & _ & _ & _ & E & _); exact E).
assert (EFa : cno_F cx = frame_addr ly' 1 (c_fpos cx)) by (unfold cno_F, frame_addr; rewrite EF'; reflexivity).
pose proof (ARU_AR tfibsegs B ly' S' U' W' mem' md' HARU') as HAR'.
destruct (frames_bounds tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' 1 (c_fpos cx) HAR' Hin')
  as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp. rewrite <- EFa in HF4096, HFceil, HFapp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
exists ly', S', regs', mem', md'.
split; [rewrite Ec; unfold cfg_at, w64; reflexivity|].
split; [exact HJ'|]. split; [exact HARU'|]. split; [exact Hh'|]. split; [exact HP|].
split; [exact HBK|]. split; [exact HZ|]. split; [exact HPP|].
apply (cno_after B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
  (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly' S' U' W' mem' md' (k + kc) regs' mem' xs (raZ regs)
  19 18 (c_fpos cx) (cno_sp1 cx) (cno_F cx) csF cssl HJ' HARU' Hin' EFa).
- rewrite (fsw_pres regs regs' 8%bv HP ltac:(cno_cs)), R8. reflexivity.
- lia.
- rewrite (ew_Ereg_nat regs' xs 9 9%bv eq_refl), (fsw_pres regs regs' 9%bv HP ltac:(cno_cs)),
    R9. unfold w64. apply wz. lia.
- rewrite (ew_Ereg_nat regs' xs 19 19%bv eq_refl),
    (fsw_pres regs regs' 19%bv HP ltac:(cno_cs)), R19. unfold w64. apply wz.
  unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp. lia.
- rewrite (ew_Ereg_nat regs' xs 18 18%bv eq_refl),
    (fsw_pres regs regs' 18%bv HP ltac:(cno_cs)), R18. unfold w64, cno_SF. apply wz.
  unfold kHighShadowEnd in Hs2. lia.
- lia.
- lia.
- lia.
- unfold cno_sv_chunks; cbn [seq map]; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (Hsv regs') c Hc) as Hck.
  assert (HB : Forall (fun c => -104 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0) cno_sv_chunks)
    by (unfold cno_sv_chunks; cbn [seq map]; repeat apply Forall_cons; try apply Forall_nil; cbn; lia).
  pose proof (proj1 (Forall_forall _ _) HB c Hc) as Hcb. cbv beta in Hcb.
  apply (chunk_ok_mbyte _ (mrestrict (w_H W) mem)); [|exact Hck].
  intros i Hi. apply (mbyte_of_aview tfibsegs). apply HZ; [unfold cno_zone; left; lia|].
  apply (HKs (cno_sp0 cx + YP09.c_off c + i)). lia.
- intros a Ha. reflexivity.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (HcsF regs' HP) c Hc) as Hck.
  destruct (proj1 (Forall_forall _ _) HcsFb c Hc) as (Hlo & Hhi & HnK).
  apply (chunk_ok_mbyte _ (mrestrict (w_H W) mem)); [|exact Hck].
  intros i Hi. apply (mbyte_of_aview tfibsegs). apply HZ; [unfold cno_zone; right; right; left; lia | apply HnK; exact Hi].
- exact Hwf.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (Hcssl regs' HP) c Hc) as Hck.
  destruct (proj1 (Forall_forall _ _) Hcsslb c Hc) as (Hlo & Hhi & HnK).
  apply (chunk_ok_mbyte _ (mrestrict (w_H W) mem)); [|exact Hck].
  intros i Hi. apply (mbyte_of_aview tfibsegs). apply HZ; [unfold cno_zone; right; left; lia | apply HnK; exact Hi].
Qed.

(* ---- reading a run's state ---- *)
Lemma cno_reg : forall H E ss ms (r : bv 5) n, st_ok tfibsegs E ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof. intros H E ss ms r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply fsw_SOff0. Qed.
Lemma cno_chunk_at : forall E ss H ms i r n c, st_ok tfibsegs E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some n -> In c (YP09.r_chunks r) ->
  YP09.chunk_ok tfibsegs E (mrestrict H (ms_mem ms)) (bv_unsigned (ew E n)) c.
Proof.
intros E ss H ms i r n c HS Hr Hb Hc. pose proof (fsw_region_nth _ _ _ i r HS Hr) as HR. cbn [ms_mem restrict] in HR.
destruct HR as (_ & _ & _ & Hcs). rewrite Hb in Hcs. exact (proj1 (Forall_forall _ _) Hcs c Hc).
Qed.

(* ---- the write windows of the boundary states are cno_zone; the ledger cells and the blocks lie outside it ---- *)
Lemma cno_wr_zone : forall cx E r csF cssl a,
  bv_unsigned (ew E 8) = cno_sp0 cx -> bv_unsigned (ew E 9) = cno_sp1 cx ->
  bv_unsigned (ew E 19) = cno_F cx -> bv_unsigned (ew E 18) = cno_SF cx ->
  in_wrange E (ss_mem (cno_ss r 19 18 csF cssl)) a -> cno_zone cx a.
Proof.
intros cx E r csF cssl a E8 E9 E19 E18 (rg & Hin & Hw).
unfold cno_ss, fss_ret_s0_args, fss_ret_s0_regs, fs_ret_s0_region, cno_fr_region, cno_sh_region, cno_sl_region in Hin.
cbn [ss_mem] in Hin. unfold cno_zone.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
  [rewrite E8 in Hw | rewrite E19 in Hw | rewrite E18 in Hw | rewrite E9 in Hw]; lia.
Qed.
Lemma cno_zone_ledger : forall cx ly S U (W : world tfibsegs) mem md a,
  cno_base B cx -> ARU tfibsegs B ly S U W mem md -> In (1, c_fpos cx) (frames S) ->
  ly_F ly = ly_F (c_ly cx) -> inFP FS_PSTAT_FP a -> ~ cno_zone cx a.
Proof.
intros cx ly S U W mem md a Hb HARU Hin EF Ha Hz.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
pose proof (cno_pstat_img a Ha) as Hi.
assert (Hb' : a < 0x5fd000).
{ destruct Ha as (q & Hq & Hq2). unfold FS_PSTAT_FP in Hq.
  destruct Hq as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hq2; lia. }
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (H4096 & Hceil & Happ).
rewrite EFa in H4096, Hceil, Happ. change (fs_frame_bytes 1) with 128 in H4096, Hceil, Happ.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
unfold cno_zone, cno_SF in Hz. unfold kLowMemEnd in Hs1. destruct Hz as [Hz | [Hz | [Hz | Hz]]].
- cno_lia.
- cno_lia.
- assert (Hr : frame_addr ly 1 (c_fpos cx) <= a < frame_addr ly 1 (c_fpos cx) + fs_frame_bytes 1)
    by (rewrite EFa; change (fs_frame_bytes 1) with 128; lia).
  exact (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) a HAR Hin Hr Hi).
- cno_lia.
Qed.
Lemma cno_zone_blk : forall cx ly S U (W : world tfibsegs) mem md p n i,
  cno_base B cx -> ARU tfibsegs B ly S U W mem md -> In (1, c_fpos cx) (frames S) ->
  ly_F ly = ly_F (c_ly cx) -> In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> ~ cno_zone cx (p + i).
Proof.
intros cx ly S U W mem md p n i Hb HARU Hin EF Hp Hi Hz.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (fsw_ablock_low B ly S W (unpoison U mem) md p n HAR Hp) as (L1 & L2 & L3).
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md p n 1 (c_fpos cx) HAR Hp Hin) as Hd.
rewrite EFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (fsw_ablock_off_shadow B ly S W (unpoison U mem) md p n HAR Hp (p + i) ltac:(lia)) as Hns.
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (H4096 & Hceil & Happ).
rewrite EFa in H4096, Hceil, Happ. change (fs_frame_bytes 1) with 128 in H4096, Hceil, Happ.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
unfold cno_zone, cno_SF in Hz. unfold shadow_addr, SHADOW_OFF in *.
destruct Hz as [Hz | [Hz | [Hz | Hz]]]; try lia; apply Hns; Z.div_mod_to_equations; lia.
Qed.
(* a run from a boundary state keeps the ledger cells and the bytes of every live block *)
Lemma cno_run_keeps : forall cx E r csF cssl ly S U (W : world tfibsegs) mem md (m m' : word -> option byte),
  cno_base B cx -> ARU tfibsegs B ly S U W mem md -> In (1, c_fpos cx) (frames S) ->
  ly_F ly = ly_F (c_ly cx) ->
  bv_unsigned (ew E 8) = cno_sp0 cx -> bv_unsigned (ew E 9) = cno_sp1 cx ->
  bv_unsigned (ew E 19) = cno_F cx -> bv_unsigned (ew E 18) = cno_SF cx ->
  frame_of E (ss_mem (cno_ss r 19 18 csF cssl)) m m' ->
  (forall a, inFP FS_PSTAT_FP a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) /\
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     m' (Z_to_bv 64 (p + i)) = m (Z_to_bv 64 (p + i))).
Proof.
intros cx E r csF cssl ly S U W mem md m m' Hb HARU Hin EF E8 E9 E19 E18 HF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
split.
- intros a Ha. apply HF. assert (Ha64 : 0 <= a < 2 ^ 64).
  { pose proof (fs_segs_low a (cno_pstat_img a Ha)). unfold kLowMemEnd in *. lia. }
  rewrite (wz a Ha64). intros Hw.
  exact (cno_zone_ledger cx ly S U W mem md a Hb HARU Hin EF Ha (cno_wr_zone cx E r csF cssl a E8 E9 E19 E18 Hw)).
- intros p n i Hp Hi. apply HF.
  destruct (fsw_ablock_low B ly S W (unpoison U mem) md p n HAR Hp) as (L1 & L2 & L3).
  rewrite (wz (p + i) ltac:(lia)). intros Hw.
  exact (cno_zone_blk cx ly S U W mem md p n i Hb HARU Hin EF Hp Hi
    (cno_wr_zone cx E r csF cssl _ E8 E9 E19 E18 Hw)).
Qed.
(* bytes, as the views read them, kept through the machine memory *)
Lemma cno_zbytes_kept : forall (W W' : world tfibsegs) m m' p (l : list Z),
  (forall j, 0 <= j < Z.of_nat (length l) -> aview tfibsegs (w_H W') m' (p + j) = aview tfibsegs (w_H W) m (p + j)) ->
  zbytes_at tfibsegs W m p l -> zbytes_at tfibsegs W' m' p l.
Proof.
intros W W' m m' p l HK Hz j Hj. destruct (Hz j Hj) as (Hv & Hr). split; [|exact Hr].
intros q Hq. assert (q = 0%nat) as -> by lia.
rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W') m m'); [exact (Hv 0%nat Hq)|].
rewrite Z.add_0_r. apply HK. lia.
Qed.
(* ---- small helpers of the chain ---- *)
Lemma cno_env_saved : forall cx r1 r2 A1 B1 T1 A2 B2 T2 j, (j < 13)%nat ->
  ew (cno_env cx r2 A2 B2 T2) (33 + j) = ew (cno_env cx r1 A1 B1 T1) (33 + j).
Proof.
intros cx r1 r2 A1 B1 T1 A2 B2 T2 j Hj. unfold cno_env. change (33 + j)%nat with (32 + S j)%nat.
rewrite !ew_Ereg_extra. do 13 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma cno_bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. intros l1 l2. unfold bsum. induction l1 as [|x l IH]; cbn [app fold_right]; lia. Qed.

(* the write window of a run from a boundary state (FSW_check_no_overread.v cno_awr, at the boundary's regions) *)
Lemma cno_awr_ss : forall E STK sp0 FP bl0 blc ly fr0 pos F sp1 r csF cssl,
  bv_unsigned (ew E 8) = sp0 -> bv_unsigned (ew E 19) = F -> bv_unsigned (ew E 18) = shadow_addr F ->
  bv_unsigned (ew E 9) = sp1 -> F = frame_addr ly 1 pos -> 104 <= STK -> sp0 - STK <= sp1 + 16 -> sp1 + 56 <= sp0 ->
  awr_ok tfibsegs B E (ss_mem (cno_ss r 19 18 csF cssl)) STK sp0 FP bl0 blc ly [(1, pos)] fr0.
Proof.
intros E STK sp0 FP bl0 blc ly fr0 pos F sp1 r csF cssl E8 EF ES E9 HF HSTK Hw1 Hw2.
exact (cno_awr B E STK sp0 FP bl0 blc ly fr0 pos 19 18 F sp1 cno_sv_chunks csF [] cssl E8 EF ES E9 HF HSTK Hw1 Hw2).
Qed.

Lemma cno_reg_off : forall H E ss ms (r : bv 5) n z v, st_ok tfibsegs E ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n z -> ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  getr (ms_regs ms) r = w64 (v + z).
Proof.
intros H E ss ms r n z v HS Hr Hn Hv Hvz.
pose proof (fsw_reg_off H E ss ms r n z v HS Hr ltac:(rewrite Hn; unfold w64; apply wz; lia) Hvz) as X.
rewrite <- X. unfold w64. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

End H.

Section V. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* a machine-level boundary: the machine (regs, mem) at a callee's entry pc *)
Definition cno_minv : Type :=
  cnocx -> Z -> alayout -> astate -> list (Z * Z) -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model ->
  Prop.
Definition cno_at (pc : Z) (INV : cno_minv) : Prop :=
  forall (cx : cnocx) k ly S U (W : world tfibsegs) regs mem md,
  cno_base B cx -> INV cx k ly S U W regs mem md ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (cno_post B cx).

(* what every boundary has: the journal, ARU and the heads at U; the registers check_no_overread keeps (sp = s1 =
   sp1, s0 = sp0, s2 = the frame's shadow, s3 = the frame, gp / tp the entry's); the thirteen saved words (the entry
   values of ra, s0, s1 .. s11, at sp0 - 8 .. sp0 - 104, in cno_saved_regs order); the frame's flag word at F + 120
   (the flag address, written by __asan_stack_malloc_1); the frame address in the slot sp1 + 0x10 (0x8133c) and the
   first past_nul result A in the slot sp1 + 0x18 (0x812fc) *)
Definition cno_mframe (cx : cnocx) (k : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (A : Z) : Prop :=
  cno_J B cx k ly S W (unpoison U mem) md /\ ARU tfibsegs B ly S U W mem md /\ FSupoisonU.fs_heads B ly S U /\
  getr regs 2 = w64 (cno_sp1 cx) /\ getr regs 8 = w64 (cno_sp0 cx) /\ getr regs 9 = w64 (cno_sp1 cx) /\
  getr regs 18 = w64 (cno_SF cx) /\ getr regs 19 = w64 (cno_F cx) /\
  getr regs 3 = getr (c_regs cx) 3 /\ getr regs 4 = getr (c_regs cx) 4 /\
  (forall j, (j < 13)%nat ->
     val_mem tfibsegs (mrestrict (w_H W) mem) (cno_sp0 cx - 8 * (Z.of_nat j + 1)) 8
       (bv_unsigned (getr (c_regs cx) (nth j cno_saved_regs 0%bv)))) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 120) 8 (bv_unsigned (w64 (cno_FL cx))) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_sp1 cx + 16) 8 (cno_F cx) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_sp1 cx + 24) 8 A.

(* the slot chunks of a resume state past 0x8133c: the frame address at 0x10, a at 0x18 *)
Definition cno_sl10 : list YP09.chunk := [YP09.mkChunk 16 (CVal 8 (SOff 19 0)); YP09.mkChunk 24 (CVal 8 (SOff 48 0))].
(* the env's extra words at a resume past the three raw blocks (atoms 32 .. 50), then the segment's own (51 ..) *)
Definition cno_xs (cx : cnocx) (A Bp T : Z) (extra : list word) : list word :=
  fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) A Bp T ++ extra.

(* the call step's pre from a boundary machine *)
Lemma cno_site_of_mframe : forall cx k ly S U (W : world tfibsegs) regs mem md A r,
  cno_mframe cx k ly S U W regs mem md A -> getr regs 1 = w64 r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  cno_site B cx k ly S U W regs mem md.
Proof.
intros cx k ly S U W regs mem md A r (HJ & HARU & Hh & R2 & R8 & R9 & R18 & R19 & R3 & R4 & Hsv & _) R1 Hr Hr2.
split; [exact HJ|]. split; [exact HARU|]. split; [exact Hh|].
split; [exact R2|]. split; [exact R8|]. split; [exact R3|]. split; [exact R4|].
split; [rewrite R1; apply ret_ok_even; unfold w64; rewrite unsigned_lit_small by lia; exact Hr2|].
split; [unfold raZ; rewrite R1; unfold w64; rewrite unsigned_lit_small by lia; lia|].
split.
- pose proof (Hsv 0%nat ltac:(lia)) as X. cbn [nth cno_saved_regs Z.of_nat] in X.
  replace (cno_sp0 cx - 8 * (0 + 1)) with (cno_sp0 cx - 8) in X by lia.
  exact (ACem.rdword_of_val_mem tfibsegs _ _ _ _ X (u64_range _)).
- pose proof (Hsv 1%nat ltac:(lia)) as X. cbn [nth cno_saved_regs Z.of_nat] in X.
  replace (cno_sp0 cx - 8 * (1 + 1)) with (cno_sp0 cx - 16) in X by lia.
  exact (ACem.rdword_of_val_mem tfibsegs _ _ _ _ X (u64_range _)).
Qed.

(* the resume after a call from a boundary machine: cno_resume with the boundary's chunks (the saved words, the flag
   word, the slots 0x10 / 0x18), read from cno_mframe, under the env Ereg regs' (cno_xs cx A Bp T extra) *)
Lemma cno_mframe_resume : forall cx k ly S U (W : world tfibsegs) regs mem md A Bp T extra kc U' (Kp : Z -> Prop)
  (P : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  cno_base B cx -> cno_mframe cx k ly S U W regs mem md A -> cno_site B cx k ly S U W regs mem md ->
  0 <= A < 2 ^ 64 -> cno_ret B cx k ly S regs mem W kc U' Kp P W' c' ->
  (forall a, cno_sp0 cx - 104 <= a < cno_sp0 cx -> ~ Kp a) ->
  (forall i, 0 <= i < 8 -> ~ Kp (cno_F cx + 120 + i)) ->
  (forall i, 0 <= i < 16 -> ~ Kp (cno_sp1 cx + 16 + i)) ->
  exists ly' S' regs' mem' md',
    c' = mkCfg (mkst regs' (Z_to_bv 64 (raZ regs)) mem' (seg_rom tfibsegs)) md' /\
    cno_J B cx (k + kc) ly' S' W' (unpoison U' mem') md' /\ ARU tfibsegs B ly' S' U' W' mem' md' /\
    FSupoisonU.fs_heads B ly' S' U' /\ aregs_preserved regs regs' /\
    (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
       ~ Kp (p + i) -> aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) mem (p + i)) /\
    (forall a, cno_zone cx a -> ~ Kp a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
    P ly' S' W' regs' mem' md' /\
    st_ok tfibsegs (Ereg regs' (cno_xs cx A Bp T extra)) (cno_ss (raZ regs) 19 18 cno_flag_chunk cno_sl10)
      (restrict (w_H W') (mkst regs' (Z_to_bv 64 (raZ regs)) mem' (seg_rom tfibsegs))).
Proof.
intros cx k ly S U W regs mem md A Bp T extra kc U' Kp P W' c' Hb Hm Hs HA Hret HKs HKf HKl.
pose proof Hm as (HJ & HARU & _ & R2 & R8 & R9 & R18 & R19 & R3 & R4 & Hsv & HFL & HS16 & HS24).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (frames_bounds tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
apply (cno_resume B cx k ly S U W regs mem md kc U' Kp P W' c' (cno_xs cx A Bp T extra) cno_flag_chunk cno_sl10
  Hb Hs Hret R9 R18 R19 HKs).
- vm_compute. reflexivity.
- intros regs'. unfold cno_sv_chunks. cbn [seq map].
  assert (HX : forall j, (j < 13)%nat ->
    YP09.chunk_ok tfibsegs (Ereg regs' (cno_xs cx A Bp T extra)) (mrestrict (w_H W) mem) (cno_sp0 cx)
      (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0)))).
  { intros j Hj. apply (chunk_ok_val tfibsegs _ _ _ _ 8%N _ (bv_unsigned (getr (c_regs cx) (nth j cno_saved_regs 0%bv)))).
    - rewrite fsw_SOff0, Z_to_bv_bv_unsigned. change (33 + j)%nat with (32 + Datatypes.S j)%nat. unfold cno_xs.
      rewrite ew_Ereg_extra. do 13 (destruct j as [|j]; [reflexivity|]). lia.
    - apply u64_range.
    - cbn. lia.
    - replace (cno_sp0 cx + - 8 * (Z.of_nat j + 1)) with (cno_sp0 cx - 8 * (Z.of_nat j + 1)) by lia. exact (Hsv j Hj). }
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk _ (CVal _ (SOff ?n _))) =>
    let j := eval cbv in (n - 33)%nat in exact (HX j ltac:(cbv; lia)) end.
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i Hi. exact (HKf i Hi).
- constructor; [|constructor; [|apply Forall_nil]]; cbn; (split; [lia|]); (split; [lia|]); intros i Hi.
  + exact (HKl i ltac:(lia)).
  + replace (cno_sp1 cx + 24 + i) with (cno_sp1 cx + 16 + (8 + i)) by lia. exact (HKl (8 + i) ltac:(lia)).
- intros regs' _. constructor; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs _ _ _ _ 8%N _ (bv_unsigned (w64 (cno_FL cx)))); [| | cbn; lia | exact HFL].
  + rewrite fsw_SOff0, Z_to_bv_bv_unsigned. change 46%nat with (32 + 14)%nat. unfold cno_xs. rewrite ew_Ereg_extra.
    reflexivity.
  + apply u64_range.
- intros regs' HP. constructor; [|constructor; [|apply Forall_nil]].
  + apply (chunk_ok_val tfibsegs _ _ _ _ 8%N _ (cno_F cx)); [| | cbn; lia | exact HS16].
    * rewrite fsw_SOff0, (ew_Ereg_nat regs' _ 19 19%bv eq_refl), (fsw_pres regs regs' 19%bv HP ltac:(cno_cs)), R19.
      reflexivity.
    * exact HF64.
  + apply (chunk_ok_val tfibsegs _ _ _ _ 8%N _ A); [| exact HA | cbn; lia | exact HS24].
    rewrite fsw_SOff0. change 48%nat with (32 + 16)%nat. unfold cno_xs. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* the three raw blocks of the walk: a = past_nul (d, len, 'A'), b = past_nul (d, len, 'B'), t = __wrap_malloc
   (len + 18), appended in that order to the entry's blocks *)
Definition cno_raw (cx : cnocx) (a b t : Z) : list (Z * Z) := [(a, cno_n cx + 18); (b, cno_n cx + 18); (t, cno_n cx + 18)].

(* ---- INV_D1: the first preset_base64_decode call (0x81398; a0 = a, a1 = F + 0x20, ra = 0x8139c). k = 3 (two
   past_nul, one __wrap_malloc); t holds d's bytes (0x81338), 17 zeros (0x81354) and 0 (0x81374); the three
   locals F + 0x20 / 0x40 / 0x60 are 0 (0x8137c / 0x81384 / 0x8138c) and their granules addressable (the
   lifetime-start stores 0x81378 / 0x81380 / 0x81388 write their shadow bytes 00); s4 = b, s5 = t, s7 = F + 0x40,
   s10 = F + 0x20, s11 = F + 0x60 ---- *)
Definition INV_D1 : cno_minv := fun cx k ly S U W regs mem md => exists a b t,
  U = c_U cx /\ k = 3 /\ cno_mframe cx k ly S U W regs mem md a /\
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t /\
  getr regs 1 = w64 0x8139c /\ getr regs 10 = w64 a /\ getr regs 11 = w64 (cno_F cx + 32) /\
  getr regs 20 = w64 b /\ getr regs 21 = w64 t /\ getr regs 23 = w64 (cno_F cx + 64) /\
  getr regs 26 = w64 (cno_F cx + 32) /\ getr regs 27 = w64 (cno_F cx + 96) /\
  zbytes_at tfibsegs W mem a (pn_copy (c_db cx) 65) /\ zbytes_at tfibsegs W mem b (pn_copy (c_db cx) 66) /\
  zbytes_at tfibsegs W mem t (c_db cx ++ repeat 0 18%nat) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 32) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 64) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 96) 8 0 /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (cno_F cx + 32) 8 /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (cno_F cx + 64) 8 /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (cno_F cx + 96) 8 /\
  fs_glob tfibsegs W mem (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx).

(* ---- INV_F1: the first fuzz_free call (0x81420; a0 = r1, ra = 0x81424), r1 / r2 / r3 the three decode results
   (s6 / s8 / s9), decided at once by b64_dec db (the same text db each time): all 0 on a bad text (k = 3 + 3 * 2),
   else three reader blocks of dec_size db bytes, each holding the decoded bytes (k = 3 + 3); cnt + 3 either way ---- *)
Definition INV_F1 : cno_minv := fun cx k ly S U W regs mem md => exists a b t peak',
  cno_mframe cx k ly S U W regs mem md a /\
  getr regs 1 = w64 0x81424 /\ getr regs 20 = w64 b /\ getr regs 21 = w64 t /\
  c_peak cx <= peak' /\
  ((WriterSpec.b64_dec (c_db cx) = None /\ U = c_U cx /\ k = 3 + 3 * EV_preset_base64_decode /\
    ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t /\
    getr regs 10 = w64 0 /\ getr regs 22 = w64 0 /\ getr regs 24 = w64 0 /\ getr regs 25 = w64 0 /\
    fs_glob tfibsegs W mem (c_live cx) peak' (c_cnt cx + 3) (c_fail cx))
   \/
   (exists out q1 q2 q3, WriterSpec.b64_dec (c_db cx) = Some out /\
    U = c_U cx ++ [(q1 - HEAD, HEAD); (q2 - HEAD, HEAD); (q3 - HEAD, HEAD)] /\ k = 3 + 3 /\
    ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ++
      [(q1 - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD); (q2 - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD);
       (q3 - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD)] /\
    4096 + HEAD <= q1 /\ 4096 + HEAD <= q2 /\ 4096 + HEAD <= q3 /\
    getr regs 10 = w64 q1 /\ getr regs 22 = w64 q1 /\ getr regs 24 = w64 q2 /\ getr regs 25 = w64 q3 /\
    fs_rblock tfibsegs B ly S W mem q1 (FSH_Fn_writer.dec_size (c_db cx)) /\
    fs_rblock tfibsegs B ly S W mem q2 (FSH_Fn_writer.dec_size (c_db cx)) /\
    fs_rblock tfibsegs B ly S W mem q3 (FSH_Fn_writer.dec_size (c_db cx)) /\
    fs_glob tfibsegs W mem (c_live cx + 3 * FSH_Fn_writer.dec_size (c_db cx)) peak' (c_cnt cx + 3) (c_fail cx))).

(* ---- the two hand-proved segments ---- *)
Definition cno_segD_T : Prop := cno_at A_fuzz_free INV_F1 -> cno_at A_preset_base64_decode INV_D1.
Definition cno_segF_T : Prop := cno_from B cno_ss_R (INV_R B) -> cno_at A_fuzz_free INV_F1.
End V.
