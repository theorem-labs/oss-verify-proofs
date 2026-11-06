(* Made by a Theorem Labs lane (2026-10-29, a Theorem Labs lane's DRIVER_CF_B) as the image-B twin of lib/A/AD1w_cf_br.v
   (commit 46f1762ad5a): the same text over lib/B's modules and YCfn_cf.v's _b names (fr_FP_b,
   fr_live_post_b, fr_surv_b), with YCbq / YCbqG from lib/B (A2's re-pointed copies), YE2k's sink head and A2's
   YD1w_cf (fr_lib_post_drv, fr_LI). No image numeral. *)
(* The post half of the DriverCF bridge: from W8's program post at the walk header (cut_x's fr_lib_post_cf_x at
   ARx := ARcf, PST := [], the globals G := G_fr_c B in the G overlay, footprint fr_FP_b) to the driver header's
   fr_lib_post_drv (YD1w_cf.v: PST := G_fr_c B, footprint sink_token :: fr_FP_b, per-call invariant fr_LI).  The journal
   conjunct goes through the three axis steps of YD1w_cf_fp.v: ajournal_x_degag (the G overlay, with the five
   placement facts named here as premises), ajournal_x_pst_weaken (subsumed: degag lands at any PST' containing PST)
   and ajournal_x_add_sink (footprint).  W8's journal conjunct is taken UNPACKED, as ajournal_gx_x unfolds at
   XO = 0 / OUT = [] (W_journal_x.v:124: `0 <= STK /\ 0 <= 0 /\ (exists memS, ajournal_x .. W memS .. /\
   gagree G (w_H W) mem memS) /\ ..`), so this file needs no kitx file; the two-line unpacking happens at the
   composition, where cut_x is present.  W8's post must carry, after its header round (a Theorem Labs lane's announcement),
   NP S' and fr_surv_b in the memory-named form (YCfn_cf.v, _b names); this lemma takes them in exactly those forms. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G YCfn_cf YD1w_cf YD1w_cf_fp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section br.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LIBROOM : astate -> Prop.
Variable NP : astate -> Prop.
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Notation ARx := (ARcf (cp := cp) tfibsegs B).
(* W8's top_x instance: ARcf does not force Hp = [] (YG0ncf.v:610), so the walks run at the conjunction, whose laws
   are W_journal_x.AR_laws_x_and_hp (W8Entry-2, XcfFinish's measurement) *)
Local Notation ARxH := (fun ly S Hp W mem md => ARcf (cp := cp) tfibsegs B ly S Hp W mem md /\ Hp = []).
Local Notation GF := (G_fr_c B).

(* ARx occurs in ajournal_x only as its first conjunct, the post state's (YCbqG.v:216), so a journal at the
   conjunction is one at ARcf with Hp' = [].  ROUTE R: at any world relation R (ajournal_xR); the strict
   ajournal_x_hp_proj is the twin at wle. *)
Lemma ajournal_x_hp_projR {R : world segs -> world segs -> Prop} : forall PST STK sp0 FP ly S Hp (W : world segs) mem
  md own ly' S' Hp' (W' : world segs) mem' md' k,
  ajournal_xR (SK := YE2k.tfib_sink_head) segs B PST ARxH R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR (SK := YE2k.tfib_sink_head) segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k /\
  Hp' = [].
Proof.
  intros PST STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k H.
  destruct H as [[HA HH] Hr]. split; [exact (conj HA Hr) | exact HH].
Qed.
Lemma ajournal_x_hp_proj : forall PST STK sp0 FP ly S Hp (W : world segs) mem md own ly' S' Hp' (W' : world segs)
  mem' md' k,
  ajournal_x (SK := YE2k.tfib_sink_head) segs B PST ARxH STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_x (SK := YE2k.tfib_sink_head) segs B PST ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k /\
  Hp' = [].
Proof. exact (@ajournal_x_hp_projR (@wle segs)). Qed.

(* ROUTE R: the bridge at any world relation R, from W8's post at R (cut_x fr_lib_post_cf_xR, its journal
   ajournal_gx_xR unpacked) to the driver's post at R (YD1w_cf.v fr_lib_post_drvR); fr_post_bridge is its twin at wle *)
Theorem fr_post_bridgeR {R : world segs -> world segs -> Prop} : forall regs ly S Hp (W : world segs) mem md p n M ci0
  l ly' S' (W' : world segs) regs' mem' md' k,
  let Goff a := inGb GF (bv_unsigned (Z_to_bv 64 a)) = false in
  (* the five placement facts the journal's kept clauses read (ajournal_x_degag at G := PST' := G_fr_c B) *)
  (forall a, in_img segs a -> ~ Exists (in_zr a) GF -> Goff a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> Goff a) ->
  (forall p0 n0 i, In (p0, n0) (ablocks B ly S) -> 0 <= i < req_size n0 -> Goff (p0 + i)) ->
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     Goff a) ->
  (forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) -> Goff a) ->
  (* the call index, from the pre (fr_lib_pre_drv's 0 <= ci0 < 4) *)
  0 <= ci0 < 4 ->
  (* W8's post at the walk header: the journal unpacked from ajournal_gx_xR at XO = 0, OUT = [], then the rest *)
  (exists memS, ajournal_xR (SK := YE2k.tfib_sink_head) segs B [] ARxH R LLVMF_STK (spZ regs) (fr_FP_b regs ly S W mem)
     ly S Hp W memS md [] ly' S' [] W' mem' md' k /\ gagree GF (w_H W) mem memS) ->
  fr_live_post_b S S' k -> NP S' ->
  aregs_preserved regs regs' -> getr regs' 10 = w64 0 ->
  fr_surv_b B ly S W mem ly' S' W' mem' ->
  fr_gi B GF ly' S' W' mem' -> rom_view segs W' mem' ->
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) ->
  m_fs md' = ll_fs l -> ll_ret l = 0 -> ll_out l = [] -> Fs.fs_sorted (ll_fs l) = true ->
  asink_none segs tfib_K (rd W' mem') md' ->
  ameta_inv segs tfib_K ly' (rd W' mem') M ->
  mo_le MT S S' (XN_LIB n) ->
  (forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) ->
  List.NoDup (fr_hblks_b W' mem') /\ incl (fr_hblks_b W' mem') (ablocks B ly' S') ->
  fr_xcnt_ok_b B ly' S' W' mem' (if n =? 0 then [] else [(p, n)]) ->
  fr_capout_ok_b W' mem' ->
  (* field round 3 (Part A): the RELRO bytes at the return (the caller has them from the post journal's ARX) *)
  YG0dcf.arodata_ok_cf segs B mem' ->
  fr_lib_post_drvR (cp := cp) B MT XN_LIB NP R regs ly S Hp W mem md p n M ci0 l ly' S' W' regs' mem' md' k.
Proof.
  intros regs ly S Hp W mem md p n M ci0 l ly' S' W' regs' mem' md' k Goff HGP HGC HGB HGF HGE Hci
    (memS & HJ & Hag) Hlp HNP Hrp Hr10 Hsv Hgi Hrv Hfd Hfs Hret Hout Hsort Hsk Hmeta Hmo Hin HHFP HXC HCAP HAD.
  unfold fr_lib_post_drvR. split.
  - apply ajournal_x_add_sinkR.
    exact (ajournal_x_degagR segs B [] ARx GF GF memS LLVMF_STK (spZ regs) (fr_FP_b regs ly S W mem) ly S Hp W mem md
      [] ly' S' [] W' mem' md' k (fun r Hr => match Hr with end) HGP HGC HGB HGF HGE Hag
      (proj1 (ajournal_x_hp_projR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))).
  - refine (conj Hlp (conj HNP (conj Hrp (conj Hr10 (conj Hsv (conj _ (conj Hrv (conj Hfd (conj Hfs (conj Hret
      (conj Hout (conj Hsort (conj Hsk (conj Hmeta (conj Hmo (conj Hin (conj HHFP (conj HXC (conj HCAP HAD))))))))))))))))))).
    unfold fr_LI. split; [lia | exact Hgi].
Qed.
Theorem fr_post_bridge : forall regs ly S Hp (W : world segs) mem md p n M ci0 l ly' S' (W' : world segs) regs'
  mem' md' k,
  let Goff a := inGb GF (bv_unsigned (Z_to_bv 64 a)) = false in
  (* the five placement facts the journal's kept clauses read (ajournal_x_degag at G := PST' := G_fr_c B) *)
  (forall a, in_img segs a -> ~ Exists (in_zr a) GF -> Goff a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> Goff a) ->
  (forall p0 n0 i, In (p0, n0) (ablocks B ly S) -> 0 <= i < req_size n0 -> Goff (p0 + i)) ->
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     Goff a) ->
  (forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) -> Goff a) ->
  (* the call index, from the pre (fr_lib_pre_drv's 0 <= ci0 < 4) *)
  0 <= ci0 < 4 ->
  (* W8's post at the walk header: the journal unpacked from ajournal_gx_x at XO = 0, OUT = [], then the rest *)
  (exists memS, ajournal_x (SK := YE2k.tfib_sink_head) segs B [] ARxH LLVMF_STK (spZ regs) (fr_FP_b regs ly S W mem)
     ly S Hp W memS md [] ly' S' [] W' mem' md' k /\ gagree GF (w_H W) mem memS) ->
  fr_live_post_b S S' k -> NP S' ->
  aregs_preserved regs regs' -> getr regs' 10 = w64 0 ->
  fr_surv_b B ly S W mem ly' S' W' mem' ->
  fr_gi B GF ly' S' W' mem' -> rom_view segs W' mem' ->
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) ->
  m_fs md' = ll_fs l -> ll_ret l = 0 -> ll_out l = [] -> Fs.fs_sorted (ll_fs l) = true ->
  asink_none segs tfib_K (rd W' mem') md' ->
  ameta_inv segs tfib_K ly' (rd W' mem') M ->
  mo_le MT S S' (XN_LIB n) ->
  (forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) ->
  List.NoDup (fr_hblks_b W' mem') /\ incl (fr_hblks_b W' mem') (ablocks B ly' S') ->
  fr_xcnt_ok_b B ly' S' W' mem' (if n =? 0 then [] else [(p, n)]) ->
  fr_capout_ok_b W' mem' ->
  YG0dcf.arodata_ok_cf segs B mem' ->
  fr_lib_post_drv (cp := cp) B MT XN_LIB NP regs ly S Hp W mem md p n M ci0 l ly' S' W' regs' mem' md' k.
Proof. exact (@fr_post_bridgeR (@wle segs)). Qed.
End br.
