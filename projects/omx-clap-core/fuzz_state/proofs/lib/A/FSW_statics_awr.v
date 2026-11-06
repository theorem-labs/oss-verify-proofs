(* awr_ok over the entry regions of FSW_statics' fss0TS: kit rule R2 (FSW_K.v:31-33), once, for every fs walk that
   starts at fsw_entryTS and so carries the four writable static regions of alloc.c (g_count, g_fail_at, g_live,
   g_peak).

   awr_ok_tac discharges only read-only regions and the stack region, so a run from fss0TS leaves its awr_ok goal open
   on the statics. Here the frame is awr_byte0's stack arm; the GOT word and the shadow cell have an empty write window
   (read-only); and each static is awr_byte's static arm, `inFP FP a /\ in_img tfibsegs a /\
   ~ Exists (in_zr a) (as_owned_static B)`, with in_img from FSW_statics.fs_pstat_img and the not-owned half from
   FSH_Gen.fs_pstat_not_owned out of the Section hypothesis IMG (fs_img_facts, owner RELOC).

   ONE COPY (owner ruling, 02:1xZ): single writer a Theorem Labs lane (lib/A/FSW_mf_walks.v's lane); another Theorem Labs lane and any
   other fss0TS walk import it from here. Generic in FP (any FP whose inFP contains FS_PSTAT_FP's), in the entry pc and
   frame size, and in bl0 / blc / ly / own / fr0, so one statement serves every lane.
   port-from: the region shapes of FSW_statics.v (fs_pstat_region / fsTS_regions) and FSW_K.v (fstk / fs_got_region /
   fs_bcell_region); the arm names of Reusable/YCbq.v awr_byte / awr_byte0. No rename. Relocated files: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YK04 YA0i YA0n YI04 YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YM05 YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_statics.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* fs's image facts (FSH_Rt.v fs_img_facts); owner RELOC, proved once for fs's TfibB. Only its first conjunct is used
   here, through FSH_Gen.fs_pstat_not_owned. *)
Hypothesis IMG : fs_img_facts tfibsegs B.

Lemma fsw_awr_TS : forall E (pc f STK sp0 : Z) FP bl0 blc ly own fr0,
  bv_unsigned (ew E 2) = sp0 -> 0 <= f <= STK ->
  (forall a, inFP FS_PSTAT_FP a -> inFP FP a) ->
  awr_ok tfibsegs B E (ss_mem (fss0TS pc f)) STK sp0 FP bl0 blc ly own fr0.
Proof.
intros E pc f STK sp0 FP bl0 blc ly own fr0 E2 Hf HFP a (r & Hr & Ha).
assert (STAT : forall g, In (g, g + 8) FS_PSTAT_FP -> g <= a < g + 8 ->
  awr_byte tfibsegs B STK sp0 FP bl0 blc ly own fr0 a).
{ intros g Hg Hga. assert (HinFP : inFP FS_PSTAT_FP a) by exact (inFP_FS_PSTAT_FP g Hg a Hga).
  right. left. split; [exact (HFP a HinFP)|].
  split; [exact (fs_pstat_img a HinFP) | exact (fs_pstat_not_owned tfibsegs B _ _ _ _ _ _ _ IMG a HinFP)]. }
unfold fss0TS, fss0T_args, fsT_regions_args, fsT_regions, fs_pstat_regions in Hr.
cbn [ss_mem app] in Hr.
repeat (destruct Hr as [<- | Hr]).
all: first
  [ (* In r [] *) solve [exfalso; exact Hr]
  | (* the frame: awr_byte0's stack arm *)
    solve [left; left; cbn [fstk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite E2 in Ha; lia]
  | (* the GOT word and the shadow cell: empty write window *)
    solve [exfalso; cbn [fs_got_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia]
  | solve [exfalso; cbn [fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia]
  | solve [cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (STAT G_COUNT); [vm_compute; tauto | exact Ha]]
  | solve [cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (STAT G_FAIL); [vm_compute; tauto | exact Ha]]
  | solve [cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (STAT G_LIVE); [vm_compute; tauto | exact Ha]]
  | solve [cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (STAT G_PEAK); [vm_compute; tauto | exact Ha]] ].
Qed.

(* the twin at a RESUMED T state (FSW_ret.fss_retT, after a runtime call; rs = the four statics, as every fss0TS walk
   resumes): the frame region is fstk_ret f cs, window [0, f) based at atom 2 whose value is sp0 - f, so its bytes
   [sp0 - f, sp0) are again awr_byte0's stack arm (f <= STK); the GOT word and the shadow cell are read-only; the four
   statics are the static arm. Generic in the frame chunks cs and the atom facts gf (asked by a Theorem Labs lane for its three
   resumes; fuzz_malloc's resume after poison uses it too). *)
Lemma fsw_awr_retTS : forall E (r f STK sp0 : Z) cs gf FP bl0 blc ly own fr0,
  bv_unsigned (ew E 2) = sp0 - f -> 0 <= f <= STK ->
  (forall a, inFP FS_PSTAT_FP a -> inFP FP a) ->
  awr_ok tfibsegs B E (ss_mem (fss_retT r f cs fs_pstat_regions gf)) STK sp0 FP bl0 blc ly own fr0.
Proof.
intros E r f STK sp0 cs gf FP bl0 blc ly own fr0 E2 Hf HFP a (rg & Hr & Ha).
assert (STAT : forall g, In (g, g + 8) FS_PSTAT_FP -> g <= a < g + 8 ->
  awr_byte tfibsegs B STK sp0 FP bl0 blc ly own fr0 a).
{ intros g Hg Hga. assert (HinFP : inFP FS_PSTAT_FP a) by exact (inFP_FS_PSTAT_FP g Hg a Hga).
  right. left. split; [exact (HFP a HinFP)|].
  split; [exact (fs_pstat_img a HinFP) | exact (fs_pstat_not_owned tfibsegs B _ _ _ _ _ _ _ IMG a HinFP)]. }
unfold fss_retT, fsT_ret_regions, fs_pstat_regions in Hr.
cbn [ss_mem app] in Hr.
repeat (destruct Hr as [<- | Hr]).
all: first
  [ (* In rg [] *) solve [exfalso; exact Hr]
  | (* the frame: [sp0 - f, sp0), awr_byte0's stack arm *)
    solve [left; left; cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite E2 in Ha; lia]
  | (* the GOT word and the shadow cell: empty write window *)
    solve [exfalso; cbn [fs_got_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia]
  | solve [exfalso; cbn [fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia]
  | solve [cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (STAT G_COUNT); [vm_compute; tauto | exact Ha]]
  | solve [cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (STAT G_FAIL); [vm_compute; tauto | exact Ha]]
  | solve [cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (STAT G_LIVE); [vm_compute; tauto | exact Ha]]
  | solve [cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
           apply (STAT G_PEAK); [vm_compute; tauto | exact Ha]] ].
Qed.

End a.
