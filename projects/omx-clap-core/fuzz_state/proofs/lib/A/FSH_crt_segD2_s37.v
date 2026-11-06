(* check_round_trip (fs.asan 0x81a9c, build A), WALK LANE D2, segment 37: 0x8233c -> 0x82344, the second fuzz_free.
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd21.v / sd22.v, stages St21 / St22 - the
   same two fuzz_free calls at 0x82338 and 0x82340). The function-level lookup is the one quoted in the lane head
   (internal path) (checker a Theorem Labs lane, role check, CONFIRM).

   The code (MEASURED by the engine over crt_tbl): 0x8233c `ld a0, 0x30(s1)` - the s1 slot that holds `text`, atom 48 -
   then 0x82340 `jal fuzz_free`, returning to 0x82344. The run stores nothing, so the step is the base's
   crt_seg_call (FSH_crt_site.v) at r0 = 0x8233c, A_c = A_fuzz_free, r = 0x82344, STKc = STK_fuzz_free.

   What St22 of d25a984c903 does at this call, restated in S0's ajournal / ARU / U form:
   - the callee frees text's reader block (text - HEAD, enc_size len + HEAD), the last block of the walk that has a
     user-poisoned head, so the head (text - HEAD, HEAD) leaves U and U is the entry's c_U again (up to order);
   - g_live goes down by enc_size len, back to the entry's c_live;
   - the callee's footprint is fs's statics plus the freed block (fuzz_free_spec's p <> 0 arm). The statics are image
     bytes, and no image byte is a byte of a live block or of a live frame (YCbq.blk_img / frm_img); the freed block is
     apart from every other live block (YCbq.sep_blocks) and from the class-3 frame (YCbq.sep_block_frame). So the
     frame's flag word and every other block survive the call, and the freed block is a block the walk allocated
     itself (in_tmp_block: it is not one of the entry's blocks, because the boundary's block list holds it once).

   The parts both fuzz_free crossings of the lane share (segment 36 is the other) are in Section ff below, so the
   segment 36 file imports this one: crtD2ff_room, crtD2ff_fp and
   crtD2ff_call (the callee's SRr into fuzz_free_spec's post, its FP relation, flag-word safety, and what its p <> 0
   arm leaves). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret
FSW_frame FSW_frame3 FSW_rd FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site
FSH_crt_segD FSH_crt_segD2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the run: from the store-free state crt_ss2 0x8233c to the fuzz_free call =================
   MEASURED: pc A_fuzz_free (0x82d40), ra 0x82344, a0 = atom 48 (text), s8 = atom 24 (same), the two regions
   unchanged *)
Definition crtD2_ss37c : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_fuzz_free (crt_ss2 0x8233c)).
Lemma crtD2_ss37c_run : sym_run_toN tfibsegs crt_tbl FUEL A_fuzz_free (crt_ss2 0x8233c) = (crtD2_ss37c, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD2_ss37c_site : crt_csite crtD2_ss37c A_fuzz_free 0x82344.
Proof. unfold crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD2_ss37c_regs : sr_get (ss_regs crtD2_ss37c) 10%bv = SOff 48 0 /\ sr_get (ss_regs crtD2_ss37c) 24%bv = SOff 24 0.
Proof. split; vm_compute; reflexivity. Qed.

Section ff. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis FUZZ_FREE : @fuzz_free_spec fx rc SK tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- fuzz_free's room premise `st_nev S + 1 <= EV_MAX`: crt_base's `st_nev (c_S cx) + EV_check_round_trip <= EV_MAX`,
   the journal's `st_nev S3 <= st_nev (c_S cx) + k`, and the boundary's remaining allowance ---- *)
Lemma crtD2ff_room : forall cx k ly3 S3 (W3 : world tfibsegs) mem md3,
  crt_base B cx -> crt_J SK B cx ly3 S3 W3 mem md3 k -> k + 1 <= EV_check_round_trip ->
  st_nev S3 + 1 <= EV_MAX.
Proof.
intros cx k ly3 S3 W3 mem md3 HB HJ Hk.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hn3 & _).
lia.
Qed.

(* ---- the callee's footprint FS_PSTAT_FP ++ ablocks_fp [(b, m)] for a block (b, m) the walk allocated itself: it is
   inside crt's FP relation (statics: image bytes in FS_PSTAT_FP; the block: a temporary block), it misses the
   class-3 frame (so its flag word), and it misses every OTHER live block ---- *)
Lemma crtD2ff_fp : forall cx ly3 S3 (W3 : world tfibsegs) mem md3 b m,
  AR tfibsegs B ly3 S3 W3 mem md3 -> In (b, m) (ablocks B ly3 S3) -> ~ In (b, m) (ablocks B (c_ly cx) (c_S cx)) ->
  In (3, c_pos cx) (frames S3) -> frame_addr ly3 3 (c_pos cx) = crt_F cx ->
  fsw_fp_sub B (c_ly cx) (c_S cx) ly3 S3 [(3, c_pos cx)] FS_PSTAT_FP (FS_PSTAT_FP ++ ablocks_fp [(b, m)]) /\
  (forall a, crt_F cx <= a < crt_F cx + fs_frame_bytes 3 -> ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(b, m)]) a) /\
  (forall q n, In (q, n) (ablocks B ly3 S3) -> (q, n) <> (b, m) ->
     forall a, q <= a < q + req_size n -> ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(b, m)]) a).
Proof.
intros cx ly3 S3 W3 mem md3 b m HAR Hin Hnin Hin3 EF.
assert (Hfx : forall a, inFP (ablocks_fp [(b, m)]) a -> b <= a < b + req_size m).
{ intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p' & n' & Hp & Hr).
  destruct Hp as [E|[]]. injection E as <- <-. exact Hr. }
split; [|split].
- intros a Ha. apply inFP_app in Ha as [Ha|Ha].
  + right. right. left. split; [exact Ha | exact (crt_pstat_img a Ha)].
  + right. left. exists b, m. split; [exact Hin|]. split; [exact Hnin | exact (Hfx a Ha)].
- intros a Ha HF. apply inFP_app in HF as [HF|HF].
  + apply (frm_img tfibsegs B LAWS ly3 S3 W3 mem md3 3 (c_pos cx) a HAR Hin3);
      [rewrite EF; exact Ha | exact (crt_pstat_img a HF)].
  + pose proof (Hfx a HF) as Hr.
    pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 mem md3 b m 3 (c_pos cx) HAR Hin Hin3) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF in D. lia.
- intros q n Hq Hne a Ha HF. apply inFP_app in HF as [HF|HF].
  + exact (blk_img tfibsegs B LAWS ly3 S3 W3 mem md3 q n a HAR Hq Ha (crt_pstat_img a HF)).
  + pose proof (Hfx a HF) as Hr.
    pose proof (sep_blocks tfibsegs B LAWS ly3 S3 W3 mem md3 q n b m HAR Hq Hin Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* ---- one fuzz_free call of the walk at a reader block p of size n, from the call-site facts at the call memory
   memC: fuzz_free_spec's p <> 0 arm (its U split, fs_rblock, n <= live, fs_glob at fail = SIZE_MAXZ, fs_heads and
   the room), and what the post leaves - the block list with the block removed, U with its head removed, fs_glob at
   live - n, and the footprint missing every other live block. The FP relation and the flag word are crtD2ff_fp's. ---- *)
Lemma crtD2ff_call : forall cx k ly3 S3 U3 (W3 : world tfibsegs) regsC memC mdC p n live peak cnt,
  crt_base B cx ->
  crt_J SK B cx ly3 S3 W3 (unpoison U3 memC) mdC k -> ARU tfibsegs B ly3 S3 U3 W3 memC mdC ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  fpreU tfibsegs B STK_fuzz_free ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) ->
  YK11.getr regsC 10%bv = Z_to_bv 64 p ->
  In (p - HEAD, HEAD) U3 -> FSupoisonU.fs_heads B ly3 S3 U3 ->
  fs_rblock tfibsegs B ly3 S3 W3 memC p n -> n <= live ->
  fs_glob tfibsegs W3 memC live peak cnt SIZE_MAXZ ->
  ~ In (p - HEAD, n + HEAD) (ablocks B (c_ly cx) (c_S cx)) ->
  k + 1 <= EV_check_round_trip ->
  exists FPc kc (P : world tfibsegs -> config -> Prop),
    SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regsC memC mdC) P /\
    fsw_fp_sub B (c_ly cx) (c_S cx) ly3 S3 [(3, c_pos cx)] FS_PSTAT_FP FPc /\
    (forall a, crt_F cx + fs_frame_bytes 3 - 8 <= a < crt_F cx + fs_frame_bytes 3 -> ~ inFP FPc a) /\
    (forall W' c', P W' c' -> exists ly' S' U' regs' mem' md',
       c' = mkCfg (mkst regs' (YK11.getr regsC 1%bv) mem' (seg_rom tfibsegs)) md' /\
       @ajournal rc SK tfibsegs B STK_fuzz_free (spZ regsC) FPc ly3 S3 W3 (unpoison U3 memC) mdC [] ly' S' W'
         (unpoison U' mem') md' kc /\
       upoison_ok B ly' S' U' /\ upoisoned tfibsegs W' mem' U' /\ aregs_preserved regsC regs' /\
       kc = 1 /\
       (forall q m, In (q, m) (ablocks B ly3 S3) -> (q, m) <> (p - HEAD, n + HEAD) ->
          forall a, q <= a < q + req_size m -> ~ inFP FPc a) /\
       (exists l1 l2, ablocks B ly3 S3 = l1 ++ (p - HEAD, n + HEAD) :: l2 /\ ablocks B ly' S' = l1 ++ l2) /\
       (exists V1 V2, U3 = V1 ++ (p - HEAD, HEAD) :: V2 /\ U' = V1 ++ V2) /\
       FSupoisonU.fs_heads B ly' S' U' /\ fs_glob tfibsegs W' mem' (live - n) peak cnt SIZE_MAXZ).
Proof.
intros cx k ly3 S3 U3 W3 regsC memC mdC p n live peak cnt HB HJ HARU Hfr HPRE Ha0 HUin Hheads Hrb Hnl
  Hglob Hnent Hk.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
pose proof HJ as (_ & Hly & _).
pose proof (crt_F_ly cx _ ly3 Hly) as EF.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof Hrb as (Hblk & _).
destruct (crtD2ff_fp cx ly3 S3 W3 (unpoison U3 memC) mdC (p - HEAD) (n + HEAD) HAR Hblk Hnent Hin3 EF)
  as (HFP & HFF & HFB).
destruct (fsw_rblock_low B ly3 S3 W3 (unpoison U3 memC) mdC memC p n HAR Hrb) as (Hp4096 & _).
assert (Hp0 : p <> 0) by (unfold HEAD in Hp4096; lia).
apply in_split in HUin as (U1 & U2 & HU).
pose proof (FUZZ_FREE ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) p n live peak cnt SIZE_MAXZ Ha0 Hglob Hheads
  (or_intror (conj Hp0 (ex_intro _ U1 (ex_intro _ U2 (conj HU (conj HPRE (conj Hrb Hnl)))))))
  (fun _ => crtD2ff_room cx k ly3 S3 W3 _ mdC HB HJ Hk)) as HSR.
exists (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, n + HEAD)]), 1.
eexists. split; [exact HSR|]. split; [exact HFP|]. split.
{ intros a Ha. pose proof crt_frame3 as F3. exact (HFF a ltac:(lia)). }
intros W' c' [(Hz & _) | (_ & V1 & V2 & HV & HPOST)]; [exfalso; exact (Hp0 Hz)|].
destruct HPOST as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & Hbl & Hhd & Hgl).
exists ly', S', (V1 ++ V2), regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
split; [reflexivity|]. split; [exact HFB|].
split; [exact Hbl|]. split; [exists V1, V2; split; [exact HV | reflexivity]|].
split; [exact Hhd | exact Hgl].
Qed.

(* ================= segment 37: fuzz_free (text) =================
   The callee's own part (FSH_crt_site.crt_hcall): from crtD2_INV_37 at the boundary memory (every byte below
   alloc_ceiling is kept by the store-free run: text's block and fs's statics are both below it), fuzz_free_spec at
   p := c_text cx, n := enc_size len, then crtD2_INV_38 at the return: text's block and its head are gone, g_live is
   the entry's again, and the read-only view is the base's crt_rom (FSH_crt_site.v), from fs_img_facts. ---- *)
Lemma crtD2_hcall37 :
  crt_hcall SK B crtD2_ss37c A_fuzz_free 0x82344 STK_fuzz_free (crtD2_INV_37 B) (crtD2_INV_38 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJ HARU Hfr HSB RG HPRE HFRL HTOP.
destruct HINV as (same & nsame & live & peak & cnt & E24 & Hbl & Hhd & Hheads & Hrb & Hgl & _ & Hlive & Hcnt & Hk).
unfold crtD2_blocks in Hbl. unfold crtD2_heads in Hhd.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
destruct crtD2_ss37c_regs as (G10 & G24).
pose proof (crt_live0 B cx HB) as Hl0.
set (len := Z.of_nat (length (c_bs cx))) in *.
set (enc := FSH_Fn_writer.enc_size len) in *.
(* the data at the call memory: the run kept every byte below alloc_ceiling *)
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (c_text cx) enc HAR HSB Hrb) as HrbC.
pose proof (fs_glob_below W3 (ms_mem ms3) memC live peak cnt SIZE_MAXZ HSB Hgl) as HglC.
pose proof HrbC as (_ & _ & Henc & _).
(* text's block is not one of the entry's: the boundary's list holds it once *)
pose proof (crtD2_once B ly3 S3 W3 (unpoison U3 memC) mdC (ablocks B (c_ly cx) (c_S cx))
  [(c_want cx, enc); (same, nsame)] (c_text cx - HEAD, enc + HEAD) HAR Hbl) as Honce.
assert (Hnent : ~ In (c_text cx - HEAD, enc + HEAD) (ablocks B (c_ly cx) (c_S cx)))
  by (intros H; apply Honce; apply in_or_app; left; exact H).
assert (HUin : In (c_text cx - HEAD, HEAD) U3).
{ apply (Permutation_in _ (Permutation_sym Hhd)). apply in_or_app. right. left. reflexivity. }
assert (Ha0 : YK11.getr regsC 10%bv = Z_to_bv 64 (c_text cx))
  by (rewrite RG, G10, fsw_SOff0; exact (crt_E_text cx E HE)).
assert (Hk1 : k + 1 <= EV_check_round_trip) by (unfold EV_fuzz_free, CRT_EV_WRAP in Hk; lia).
destruct (crtD2ff_call cx k ly3 S3 U3 W3 regsC memC mdC (c_text cx) enc live peak cnt HB HJ HARU Hfr HPRE
  Ha0 HUin Hheads HrbC ltac:(lia) HglC Hnent Hk1) as (FPc & kc & P & HSR & HFP & HFL & HK).
exists FPc, kc, P. split; [exact HSR|]. split; [exact HFP|]. split; [exact HFL|].
intros W' c' HPc.
destruct (HK W' c' HPc) as (ly' & S' & U' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & Ekc & _ &
  (l1 & l2 & El1 & El2) & (V1 & V2 & HV & EU') & Hheads' & Hgl').
exists ly', S', U', regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'. subst kc.
unfold crtD2_INV_38. cbn [ms_mem mkst]. cbv zeta.
exists same, nsame, peak, cnt.
split.
{ rewrite (ew_Ereg_nat regs' (crt_extra cx) 24 24%bv eq_refl).
  assert (R24 : YK11.getr regs' 24%bv = YK11.getr regsC 24%bv) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
  rewrite R24, RG, G24, fsw_SOff0. exact E24. }
split.
{ unfold crtD2_blocks. rewrite El2. rewrite El1 in Hbl.
  exact (Permutation_app_inv l1 l2 (ablocks B (c_ly cx) (c_S cx)) [(c_want cx, enc); (same, nsame)] _ Hbl). }
split.
{ unfold crtD2_heads. rewrite EU'. rewrite HV in Hhd. exact (Permutation_app_inv V1 V2 (c_U cx) [] _ Hhd). }
split; [exact Hheads'|].
split; [replace (c_live cx) with (live - enc) by lia; exact Hgl'|].
split; [exact (crt_rom SK B IMG cx (k + 1) ly' S' U' W' mem' md' HB HJ' HARU')|].
split; [exact Hcnt|].
unfold EV_fuzz_free in Hk. lia.
Qed.

(* ---- the segment lemma ---- *)
Lemma crtD2_seg37 : crt_from SK B crt_ss38 (crtD2_INV_38 B) -> crt_from SK B crt_ss37 (crtD2_INV_37 B).
Proof.
intros NEXT.
exact (crt_seg_call SK B 0x8233c A_fuzz_free 0x82344 crtD2_ss37c (crtD2_INV_37 B) (crtD2_INV_38 B) STK_fuzz_free
  crtD2_ss37c_run crtD2_ss37c_site ltac:(lia) ltac:(reflexivity) (proj1 (proj2 crtD2_stk_pos)) crtD2_stk_fuzz_free
  crtD2_hcall37 NEXT).
Qed.
End ff.
