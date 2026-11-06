(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) parse_items' two grow calls on image B:
     pib_call_grow 0x84fb0 : the first member's grow call (jal 0x84fac, ra 0x84fb0; stage B's member arm stops there);
     pib_call_grow 0x85250 : a later member's grow call (jal 0x8524c, ra 0x85250; segment Ic stops there).
   Port of the A walk's lib/A/FSW_parse_items_grow.v:
   pib_after_callT is a B-local copy of its pig_after_callT (the T resume after a callee whose journal is at its own sp,
   at the caller's raised top ot), verbatim but for the name; pib_xs_nth / pib_val_eq copy pig_xs_nth / pig_val_eq; pib_grow_at / pib_call_grow port pig_call_at / pig_call
   to B: the call registers are s0 = q + 16, s1 = q, s3 = v, a0 = v (B's resume atoms q at 9, v at 19), the chain
   grow's fpreU reads at s0 = q + 16 is built here (FSW_parse_items_mem.pim_chain_q16, from in->p and in->end at q,
   q + 8; added premise p <= q), the resume state is fss_retT r 144 cs pib_rs pib_gf under pib_xs
   (FSW_parse_items_seg.v), and in->depth is k + 1 in [1, 2].
   Section hypotheses: HSS : FsShadowSyms B and HGROW : grow_spec tfibsegs B. rule 24: no function proved here. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_rres FSPstat FSH_Fn_reader FSW_rd FSW_pj FSW_K3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_mem FSW_parse_items_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the resume env's extra words, by index (pib_xs) *)
Lemma pib_xs_nth : forall p e d xr k' y' n cap', length xr = 13%nat ->
  let xs := pib_xs p e d xr k' y' n cap' in
  nth 0 xs (Z_to_bv 64 0) = Z_to_bv 64 p /\ nth 1 xs (Z_to_bv 64 0) = Z_to_bv 64 e /\
  nth 2 xs (Z_to_bv 64 0) = Z_to_bv 64 d /\
  nth 16 xs (Z_to_bv 64 0) = Z_to_bv 64 k' /\ nth 17 xs (Z_to_bv 64 0) = Z_to_bv 64 y' /\
  nth 18 xs (Z_to_bv 64 0) = Z_to_bv 64 n /\ nth 19 xs (Z_to_bv 64 0) = Z_to_bv 64 cap'.
Proof.
intros p e d xr k' y' n cap' Hl xs. subst xs. unfold pib_xs. cbn [app].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
change (nth 16 (?a :: ?b :: ?c :: ?l) ?z) with (nth 13 l z).
change (nth 17 (?a :: ?b :: ?c :: ?l) ?z) with (nth 14 l z).
change (nth 18 (?a :: ?b :: ?c :: ?l) ?z) with (nth 15 l z).
change (nth 19 (?a :: ?b :: ?c :: ?l) ?z) with (nth 16 l z).
rewrite !app_nth2 by lia. rewrite Hl. cbn. repeat split; reflexivity.
Qed.

Lemma pib_val_eq : forall (m m' : word -> option byte) a (n : nat) x, val_mem tfibsegs m a n x ->
  (forall j, (j < n)%nat -> mbyte tfibsegs m' (a + Z.of_nat j) = mbyte tfibsegs m (a + Z.of_nat j)) ->
  val_mem tfibsegs m' a n x.
Proof. intros m m' a n x H E j Hj. rewrite (E j Hj). exact (H j Hj). Qed.

(* ================= the T resume after a program call, at a raised window top ot (copied, see the header) ========= *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pib_after_callT : forall B STK ot FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 sf f regsC
  ly' S' U' W' regs' mem' md' kc xs cs rs gf r,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  ajournal tfibsegs B STK ot FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B STKc (spZ regsC) FP1 lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  fsw_fp_sub B ly S lyc Sc own FP FP1 ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = sf - f -> 0 < f -> 0 <= STKc -> spZ regsC mod 16 = 0 -> sf <= ot -> ot - STK <= spZ regsC - STKc ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W) memC) (sf - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem')) rs ->
  pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs' (fs_extraT ++ xs)) gf ->
  ajournal tfibsegs B STK ot FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK ot FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 sf f regsC ly' S' U' W' regs' mem' md' kc xs cs rs gf
  r Hgot Hcell HJ HARUc HJc HF OK' PO' HP Hsp Hf HSc Hal Hsf Hlo Hwf Hcs Hrs Hpd Hgf.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hhi : spZ regsC <= ot) by lia.
assert (HJ2 : ajournal tfibsegs B STK ot FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc))
  by exact (fsw_ajournal_sub5 B STK ot FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k
              STKc (spZ regsC) FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc Hlo Hhi HF).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
(* the callee journal's frames clause: bytes at or above alloc_ceiling outside its stack window are kept *)
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
(* the chunks lie in the frame [0, f): fstk_ret's chunk_inside, out of regions_wf *)
assert (Hin : forall c, In c cs -> 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f).
{ pose proof Hwf as Hw. unfold fsT_ret_regions in Hw. cbn [app regions_wf] in Hw.
  apply andb_prop in Hw as [Hw _]. unfold YP09.region_wf in Hw.
  apply andb_prop in Hw as [_ Hfa]. rewrite forallb_forall in Hfa.
  intros c Hc. pose proof (Hfa c Hc) as Hci. unfold YP09.chunk_inside, fstk_ret in Hci.
  cbn [YP09.r_lo YP09.r_hi] in Hci. apply andb_prop in Hci as [Hci _]. apply andb_prop in Hci as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1 | exact H2]. }
assert (Esp : YK11.getr regs' 2 = YK11.getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs' = sf - f) by (unfold spZ; rewrite Esp; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 2) = sf - f)
  by (rewrite (ew_Ereg_nat regs' (fs_extraT ++ xs) 2 2%bv eq_refl); exact Usp).
assert (E32 : ew (Ereg regs' (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 32) = SHADOW_OFF) by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
(* the two image cells of AR after the call, carried to the machine's own memory mem' (below the shadow: U' cannot
   touch them), as FSW_K3.fsw_after_callFPU_args *)
destruct (fsw_got_shadow B ly' S' W' (unpoison U' mem') md' Hgot Hcell HAR2) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W') (unpoison U' mem')) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly' S' U' W' mem' md' (Z_to_bv 64 x) HARU'
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W') (unpoison U' mem')) a 8 v -> val_mem tfibsegs (mrestrict (w_H W') mem') a 8 v).
{ intros a v Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W') mem') tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W') (unpoison U' mem') _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W') mem') tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W') (unpoison U' mem') _ _ Kcell)]. }
rewrite restrict_mkst_fx. unfold fss_retT, fsT_ret_regions in *. cbn [app] in *. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + (* the frame: writable by the composed journal's window, chunks kept by the callee's frames clause *)
    unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
    * apply Forall_forall. intros c Hc. pose proof (Hin c Hc) as Hci.
      pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
      apply (chunk_ok_mbyte _ (mrestrict (w_H W) memC)); [|exact Hck].
      destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs).
      rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' _ HARU') by lia.
      rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memC mdC _ HARUc) by lia.
      apply F1; [lia | intros Hx; lia].
  + (* the GOT word of the shadow base, as fsw_entryT *)
    unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + (* the shadow-base cell, as fsw_entryT *)
    unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok at 1 2. cbn [af_lo af_hi af_al2].
  rewrite E2, U32. split; [|split; [|exact Hgf]].
  + change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite <- Hsp. exact Hal.
  + rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.
End t.

(* ================= parse_items' grow call ================= *)
Section pib. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-base cells (FSH_Base.v); FSrtcellsS0 discharges it *)
Hypothesis HSS : FsShadowSyms B.
(* callee: grow (a Theorem Labs lane's B grow walk, lib/B/Prog/FSW_grow*.v on this base) *)
Hypothesis HGROW : @grow_spec fx rc SK tfibsegs B.

(* the call at ra r. Premises, in the walk's order: the caller's journal at the raised top ot and ARU / the rodata
   view / the heads at the call; the call registers (pi_run_grow1's measurement); the frame chain at s0 = q; struct
   pj_in at q (inside the caller's window, above parse_items' frame) with its three fields; v and grow_spec's own
   premises at ty = 6; pig_tmp: grow's old blocks are the caller's temporary blocks (allocated after its entry); the
   resume frame's chunks cs read at the call memory. The continuation gets the resume configuration and the facts
   a Theorem Labs lane named (07:05Z): the composed journal and grow's own journal (any kept-across-call lemma of FSW_rd
   applies to it: text bytes, rd_blocks_ok, fs_rblock), ARU at U', the T state, grow_res and grow's post, and q's 24
   bytes unchanged. *)
Definition pib_grow_at (r : Z) : Prop :=
  forall (m : nat) sp0 ot ly S U0 W0 mem0 md0 own lyc Sc Uc W memC mdC kc regsC q p e d xr
    v num str kids keys n cap live peak cnt fail cs (Q : world tfibsegs -> config -> Prop),
  let Dold0 := ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap in
  let FP := [(v, v + 56)] ++ FS_PSTAT_FP in
  let FPg := [(v + 24, v + 40); (v + 48, v + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP in
  ajournal tfibsegs B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
    lyc Sc W (unpoison Uc memC) mdC kc ->
  ARU tfibsegs B lyc Sc Uc W memC mdC -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B lyc Sc Uc ->
  YK11.getr regsC 1 = w64 r -> spZ regsC = sp0 - 144 -> sp0 mod 16 = 0 -> sp0 <= ot ->
  YK11.getr regsC 8 = w64 (q + 16) -> YK11.getr regsC 9 = w64 q -> YK11.getr regsC 19 = w64 v ->
  YK11.getr regsC 10 = w64 v ->
  YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  sp0 <= q -> q + 24 <= ot -> q mod 8 = 0 -> p <= q ->
  val_mem tfibsegs (mrestrict (w_H W) memC) q 8 p -> val_mem tfibsegs (mrestrict (w_H W) memC) (q + 8) 8 e ->
  val_mem tfibsegs (mrestrict (w_H W) memC) (q + 16) 4 d ->
  4096 <= p <= 2 ^ 47 - 2 ^ 23 -> 4096 <= e <= 2 ^ 47 - 2 ^ 23 -> 1 <= d <= 2 -> length xr = 13%nat ->
  pobj tfibsegs B lyc Sc W memC v ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) memC) v 6 num str kids keys n cap ->
  PjStruct.pj_slots_at (fun a k => In (a, k) Dold0) 6 kids keys n cap ->
  rd_blocks_ok tfibsegs B lyc Sc W memC Dold0 -> PjStruct.pj_apart Dold0 v -> incl (rd_heads Dold0) Uc ->
  (forall b, In b (rd_hblocks Dold0) -> ~ In b (ablocks B ly S)) ->
  fs_glob tfibsegs W memC live peak cnt fail -> quiet cnt fail (Z.of_nat (length (grow_tr 6 n cap))) ->
  rd_sum Dold0 <= live ->
  (n = cap -> 56 * ReaderRes.cap2 cap + HEAD < MALLOC_MAX) -> live + rd_live (grow_tr 6 n cap) < 2 ^ 64 ->
  st_nev Sc + rd_ev (grow_tr 6 n cap) <= EV_MAX -> blocks_bytes Sc + rd_live (grow_tr 6 n cap) <= LIVE_MAX ->
  regions_wf (fsT_ret_regions 144 cs pib_rs) = true ->
  (forall regs' k' y' cap', aregs_preserved regsC regs' ->
     Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ pib_xs p e d xr k' y' n cap')) (mrestrict (w_H W) memC)
       (sp0 - 144)) cs) ->
  (forall ly' S' U' W' regs' mem' md' k' y' cap' Dold Dnew,
     grow_res 6 n cap kids keys k' y' cap' Dold Dnew Uc U' ->
     ajournal tfibsegs B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
       ly' S' W' (unpoison U' mem') md' (kc + rd_ev (grow_tr 6 n cap)) ->
     ajournal tfibsegs B STK_grow (sp0 - 144) FPg lyc Sc W (unpoison Uc memC) mdC []
       ly' S' W' (unpoison U' mem') md' (rd_ev (grow_tr 6 n cap)) ->
     ARU tfibsegs B ly' S' U' W' mem' md' ->
     aregs_preserved regsC regs' -> YK11.getr regs' 10 = w64 0 ->
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ pib_xs p e d xr k' y' n cap')) (fss_retT r 144 cs pib_rs pib_gf)
       (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
     Permutation (ablocks B ly' S' ++ rd_hblocks Dold) (ablocks B lyc Sc ++ rd_hblocks Dnew) ->
     PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') v 6 num str k' y' n cap' ->
     PjStruct.pj_slots_at (fun a k => In (a, k) (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap'))
       6 k' y' n cap' ->
     rd_blocks_ok tfibsegs B ly' S' W' mem' (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
     rd_moved tfibsegs W W' memC mem' kids k' (56 * cap) -> rd_moved tfibsegs W W' memC mem' keys y' (8 * cap) ->
     pobj tfibsegs B ly' S' W' mem' v ->
     (exists peak', peak <= peak' /\
        fs_glob tfibsegs W' mem' (live + PjGrammar.held (grow_tr 6 n cap)) peak'
          (cnt + Z.of_nat (length (grow_tr 6 n cap))) fail) ->
     (forall a, q <= a < q + 24 ->
        mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memC) a) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Q.

Lemma pib_call_grow : forall r, YK0s.ret_ok (w64 r) -> 4096 <= r < 2 ^ 64 -> pib_grow_at r.
Proof.
intros r Hret Hr.
intros m sp0 ot ly S U0 W0 mem0 md0 own lyc Sc Uc W memC mdC kc regsC q p e d xr v num str kids keys n cap
  live peak cnt fail cs Q Dold0 FP FPg HJ HARU HRO HHEADS R1 Rsp Hal0 Hot R8 R9 R19 R10 R3 R4 Hq0 Hq1 Hq8 Hpq
  VP VE VD Hp He Hd Hxr HPO HHDR HSL HBLK HAPART HINCL HTMP HG HQ HRS HMAX HLIVE HEV HLV HWF HCS K.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HARU as (HAR & _ & _).
assert (FSg : STK_grow = ltac:(let x := eval vm_compute in STK_grow in exact x)) by reflexivity.
assert (HSTK : STK_grow + 144 <= STK_parse_items m)
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items; cbn [fold_right]; lia).
assert (Wv : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z) by (intros z Hz; unfold w64; apply wz; exact Hz).
destruct (fsw_pobj_low B lyc Sc W (unpoison Uc memC) mdC memC v HAR HPO) as (Lv1 & Lv2).
pose proof (fsw_pobj_off_img B lyc Sc W (unpoison Uc memC) mdC memC v HAR HPO) as Hvimg.
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Ha & _)|(_ & Ha & _)] _]; exact Ha).
assert (Hsp0 : alloc_ceiling + STK_grow + 144 <= sp0) by lia.
(* ---- the chain grow's fpreU reads: s0 = q + 16 (FSW_parse_items_mem.pim_chain_q16) ---- *)
assert (HCH : exists ch, achain lyc (aview tfibsegs (w_H W) (unpoison Uc memC)) (spZ regsC) (q + 16) ch).
{ apply (pim_chain_q16 lyc _ (spZ regsC) q e p).
  - rewrite (pim_rdword_U B lyc Sc Uc W memC mdC (q + 8) HARU) by lia.
    exact (YF0x.val_mem_rdword (w_H W) memC (q + 8) e ltac:(lia) VE).
  - rewrite (pim_rdword_U B lyc Sc Uc W memC mdC q HARU) by lia.
    exact (YF0x.val_mem_rdword (w_H W) memC q p ltac:(lia) VP).
  - lia.
  - lia.
  - exact Hq8.
  - rewrite Rsp. lia. }
destruct HCH as [ch HCH].
(* ---- grow's fpreU at the call ---- *)
assert (PRE : fpreU tfibsegs B STK_grow lyc Sc Uc W regsC memC mdC ch).
{ apply (fsw_fpreU_atFP B (STK_parse_items m + (ot - sp0)) ot FP ly S Uc W0 (unpoison U0 mem0) md0 own lyc Sc W memC mdC kc
    regsC STK_grow (sp0 - 144 - ot) ch HJ HARU HRO).
  - rewrite Rsp. lia.
  - clear - Hal0 Hal16. Z.div_mod_to_equations. lia.
  - lia.
  - rewrite FSg. lia.
  - lia.
  - rewrite R1. exact Hret.
  - unfold raZ. rewrite R1, Wv by lia. lia.
  - exact R3.
  - exact R4.
  - unfold s0Z. rewrite R8, Wv by lia. exact HCH. }
(* ---- grow's footprint inside the caller's ---- *)
destruct Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (HFPS : fsw_fp_sub B ly S lyc Sc own FP FPg).
{ intros a Ha. unfold FPg in Ha. apply inFP_app in Ha as [Ha|Ha]; [|apply inFP_app in Ha as [Ha|Ha]].
  - (* v's two slots: v's block, a frame of the caller's own, or a frame of its entry frames *)
    assert (HvA : v <= a < v + 56)
      by (destruct Ha as (rr & Hrr & Har); cbn [In] in Hrr; destruct Hrr as [<-|[<-|[]]]; cbn [fst snd] in Har; lia).
    assert (HFa : inFP FP a)
      by (unfold FP; apply inFP_app; left; exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
    destruct HPO as [[((cid & pos & Hf & _ & _ & H1 & H2) & _)|((b & bn & Hb & H1 & H2) & _)] _].
    + rewrite Hfrs in Hf. apply in_app_or in Hf as [Hf|Hf].
      * right; right; right; left. exists cid, pos. split; [exact Hf|]. left. unfold in_zr. cbn [fst snd]. lia.
      * right; right; right; right. split; [exact HFa|]. exists cid, pos. split; [exact Hf|].
        unfold in_zr, frame_rng. cbn [fst snd]. unfold frame_addr in *. rewrite HlyF in H1, H2. lia.
    + left. split; [exact HFa|]. exists b, bn. split; [exact Hb | unfold HEAD in *; lia].
  - (* grow's old blocks: temporary blocks of the caller *)
    right; left. destruct Ha as ((lo & hi) & Hin & Har). cbn [fst snd] in Har.
    unfold ablocks_fp in Hin. apply in_map_iff in Hin as ((b & bn) & Eb & Hbin). cbn [fst snd] in Eb.
    injection Eb as <- <-. exists b, bn. split; [|split; [exact (HTMP _ Hbin) | lia]].
    unfold rd_hblocks in Hbin. apply in_map_iff in Hbin as ((a0 & k0) & Eq & Hak). cbn [fst snd] in Eq.
    injection Eq as <- <-. exact (proj1 (HBLK a0 k0 Hak)).
  - (* the statics: FP image bytes *)
    right; right; left. split; [unfold FP; apply inFP_app; right; exact Ha | exact (pim_pstat_img a Ha)]. }
(* ---- the call ---- *)
eapply SRr_bind.
{ apply (HGROW lyc Sc Uc W regsC memC mdC ch v 6 num str kids keys n cap live peak cnt fail PRE HHEADS R10 HPO).
  - left. rewrite Rsp, FSg. rewrite FSg in Hsp0. lia.
  - exact HHDR.
  - exact HSL.
  - exact HBLK.
  - exact HAPART.
  - exact HINCL.
  - exact HG.
  - exact HQ.
  - exact HRS.
  - exact HMAX.
  - exact HLIVE.
  - exact HEV.
  - exact HLV. }
intros W' c' _ (k' & y' & cap' & Dold & Dnew & U' & HRES & ly' & S' & regs' & mem' & md' & -> & HJg & OK' & PO' & HP &
  (A0 & PERM & HHDR' & HSL' & HBLK' & MVK & MVY & HPO' & HG')).
set (xs := pib_xs p e d xr k' y' n cap').
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJg) | split; [exact OK' | exact PO']]).
assert (I1 : ot - (STK_parse_items m + (ot - sp0)) <= spZ regsC - STK_grow) by (rewrite Rsp; lia).
assert (I2 : spZ regsC <= ot) by (rewrite Rsp; lia).
assert (HJ2 : ajournal tfibsegs B (STK_parse_items m + (ot - sp0)) ot FP ly S W0 (unpoison U0 mem0) md0 own
    ly' S' W' (unpoison U' mem') md' (kc + rd_ev (grow_tr 6 n cap)))
  by exact (fsw_ajournal_sub5 B _ ot FP ly S W0 (unpoison U0 mem0) md0 own lyc Sc W (unpoison Uc memC) mdC kc
              STK_grow (spZ regsC) FPg [] ly' S' W' (unpoison U' mem') md' _ HJ HJg I1 I2 HFPS).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
(* q's 24 bytes: at or above alloc_ceiling and above grow's window, so grow's frames clause keeps them *)
assert (QK : forall a, q <= a < q + 24 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memC) a).
{ intros a Ha. pose proof HJg as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  apply (mbyte_of_aview tfibsegs).
  rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' a HARU') by lia.
  rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memC mdC a HARU) by lia.
  apply F1; [lia | rewrite Rsp; lia]. }
(* ---- the resume env ---- *)
assert (G9 : YK11.getr regs' 9 = w64 q) by (rewrite <- R9; exact (HP 9 ltac:(unfold acallee_saved; lia))).
assert (G19 : YK11.getr regs' 19 = w64 v) by (rewrite <- R19; exact (HP 19 ltac:(unfold acallee_saved; lia))).
assert (G2 : YK11.getr regs' 2 = YK11.getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (E9 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 9) = q).
{ rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), G9. apply Wv. lia. }
assert (E19 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 19) = v).
{ rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), G19. apply Wv. lia. }
assert (E2 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 2) = sp0 - 144).
{ rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl), G2. exact Rsp. }
destruct (pib_xs_nth p e d xr k' y' n cap' Hxr) as (X0 & X1 & X2 & X16 & X17 & X18 & X19).
assert (XA : forall j, ew (Ereg regs' (fs_extraT ++ xs)) (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; apply fsw_ew_xatom).
(* ---- grow's new blocks ---- *)
pose proof HHDR as (_ & _ & _ & _ & _ & _ & (Hn0 & _) & (Hc0 & _)).
assert (Hcp : 0 < cap').
{ destruct HSL as (_ & Hncap & _). destruct HRES as [(Hlt & _ & _ & -> & _)|(Heq & -> & _)]; [lia|].
  unfold ReaderRes.cap2. destruct (Z.eqb_spec cap 0); lia. }
pose proof HHDR' as (_ & Hty' & _ & _ & Hkids' & Hkeys' & Hn' & Hcap').
pose proof HSL' as (_ & Hncap' & _ & Hcapp').
destruct (Hcapp' Hcp) as (KIN' & YIN6). pose proof (YIN6 eq_refl) as YIN'.
pose proof (HBLK' _ _ KIN') as KRB'. pose proof (HBLK' _ _ YIN') as YRB'.
destruct (fsw_rblock_low B ly' S' W' (unpoison U' mem') md' mem' k' _ (proj1 HARU') KRB') as (K1 & K2).
destruct (fsw_rblock_low B ly' S' W' (unpoison U' mem') md' mem' y' _ (proj1 HARU') YRB') as (Y1 & Y2).
pose proof KRB' as (_ & Kal & _ & _). pose proof YRB' as (_ & Yal & _ & _).
(* ---- the two resume regions ---- *)
assert (HRSOK : Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem')) pib_rs).
{ unfold pib_rs. constructor; [|constructor; [|constructor]].
  - unfold region_ok, pi_qR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split.
    + intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
    + constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val tfibsegs _ _ q 0 8 (SOff (xatom 0) 0) p);
          [rewrite fsw_SOff0, XA; exact X0 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
        cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
        apply (pib_val_eq _ _ q 8 p VP). intros j Hj. apply QK. lia.
      * apply (chunk_ok_val tfibsegs _ _ q 8 8 (SOff (xatom 1) 0) e);
          [rewrite fsw_SOff0, XA; exact X1 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
        cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        apply (pib_val_eq _ _ (q + 8) 8 e VE). intros j Hj. apply QK. lia.
      * apply (chunk_ok_val tfibsegs _ _ q 16 4 (SOff (xatom 2) 0) d);
          [rewrite fsw_SOff0, XA; exact X2 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
        cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        apply (pib_val_eq _ _ (q + 16) 4 d VD). intros j Hj. apply QK. lia.
  - unfold pib_vR, pib_vch. apply (fsw_pj_part_okW tfibsegs _ _ 19 v v 0 56 0 56); [lia | lia | destruct HPO' as [_ Hw']; exact Hw' | exact E19
      | lia | lia | right; lia |].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
    + apply (fsw_pj_chunk4 tfibsegs _ _ v 0 (SLit 6) 6); [rewrite Z.add_0_r; exact Hty' | reflexivity].
    + apply (fsw_pj_chunk8 tfibsegs _ _ v 24 (SOff (xatom 16) 0) k'); [exact Hkids' | rewrite fsw_SOff0, XA; exact X16].
    + apply (fsw_pj_chunk8 tfibsegs _ _ v 32 (SOff (xatom 17) 0) y'); [exact Hkeys' | rewrite fsw_SOff0, XA; exact X17].
    + apply (fsw_pj_chunk8 tfibsegs _ _ v 40 (SOff (xatom 18) 0) n); [exact Hn' | rewrite fsw_SOff0, XA; exact X18].
    + apply (fsw_pj_chunk8 tfibsegs _ _ v 48 (SOff (xatom 19) 0) cap'); [exact Hcap' | rewrite fsw_SOff0, XA; exact X19]. }
assert (HPD : pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (fsT_ret_regions 144 cs pib_rs)).
{ unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pib_rs, pi_qR, pib_vR.
  cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9, E19.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (HGF : atoms_ok (Ereg regs' (fs_extraT ++ xs)) pib_gf).
{ unfold pib_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E19, !XA. unfold xs. rewrite X0, X1, X2, X16, X17, X18, X19.
  pose proof Hkids' as (Rk & _). pose proof Hkeys' as (Ry & _). pose proof Hn' as (Rn & _). pose proof Hcap' as (Rc & _).
  rewrite (wz p), (wz e), (wz d), (wz k'), (wz y'), (wz n), (wz cap') by lia.
  change (2 ^ 3) with 8. change (2 ^ 0) with 1. change (2 ^ 4) with 16.
  unfold HEAD in *.
  repeat split; try lia; try apply Z.mod_1_r; try exact Hq8; try exact Hv8; try exact Kal; try exact Yal. }
(* ---- the resume ---- *)
destruct (pib_after_callT B (STK_parse_items m + (ot - sp0)) ot FP own ly S U0 W mem0 md0 W0 lyc Sc Uc memC mdC kc
  STK_grow FPg sp0 144 regsC ly' S' U' W' regs' mem' md' (rd_ev (grow_tr 6 n cap)) xs cs pib_rs pib_gf r
  (proj1 HSS) (proj2 HSS) HJ HARU HJg HFPS OK' PO' HP Rsp ltac:(lia) ltac:(rewrite FSg; lia)
  ltac:(rewrite Rsp; clear - Hal0; Z.div_mod_to_equations; lia) Hot I1 HWF (HCS regs' k' y' cap' HP) HRSOK HPD HGF)
  as (_ & _ & HST).
rewrite R1.
rewrite Rsp in HJg.
exact (K ly' S' U' W' regs' mem' md' k' y' cap' Dold Dnew HRES HJ2 HJg HARU' HP A0 HST PERM HHDR' HSL' HBLK'
  MVK (MVY eq_refl) HPO' HG' QK).
Qed.

(* the first member's grow call: jal at 0x84fac, ra 0x84fb0 (pi_stageB_member) *)
Lemma pib_call_grow1 : pib_grow_at 0x84fb0.
Proof. apply pib_call_grow; [unfold YK0s.ret_ok; vm_compute; reflexivity | lia]. Qed.
(* a later member's grow call: jal at 0x8524c, ra 0x85250 (segment Ic) *)
Lemma pib_call_grow2 : pib_grow_at 0x85250.
Proof. apply pib_call_grow; [unfold YK0s.ret_ok; vm_compute; reflexivity | lia]. Qed.
End pib.
