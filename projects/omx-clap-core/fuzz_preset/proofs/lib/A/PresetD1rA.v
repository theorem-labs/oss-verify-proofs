(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan image A), the driver's per-call loop over preset's SECOND
   allocator instance (a Theorem Labs lane's ARcf). STATEMENTS ONLY: the proof is lib/A/PresetD1rAPf.v. Nothing here proves a
   function (rule 24: composition / driver layer of a port).
   Donor: proofs/cgif/cgif_file_fuzzer/lib/A/AD1r.v, tfib_loop_L (:1053), whose type is loop_L_x of lib/A/AD1w.v:208
   (B twin lib/YD1r.v:1056, lib/YD1w.v:206). loop_L_x_A below is the donor's tfib_loop_L TYPE, closed: every leaf the
   donor takes as a Section hypothesis is a premise, every parameter is universally quantified. Interface:
   lib/A/PresetCfnA.v (a working branch, IfacePort's room re-cut). Changes:
   (1) AR -> ARcf at the ghost head set Hp = [] (lib/Reusable/YG0ncf.v) for the loop state; the laws are a8's
       AR_laws_cf. The allocator instance's parameters are preset's: CfParams_preset (lib/A/CfParamsPreset.v),
       this file's only CfParams instance.
   (2) The donor's event room `st_nev S + EV_LIB * Z.of_nat r + 3 <= EV_MAX` goes, and so does every headroom number
       (resume brief 2026-10-29 03:48Z, design change 1: the run-level `ROOM_cf_k S (N_LLVMF * r + 2)` is
       unsatisfiable, port/n-llvmf.md). The loop's room is the interface's two STATE conjuncts, carried across the
       calls by the slot's post: iface_room_np S (the interface's Section variable, the non-primary room, owner
       a Theorem Labs lane) and PCA.iface_room_at sm x os H0 hist S (a Theorem Labs lane's P8 premises, lib/Spec/PresetP8.v
       preset_room, at the harness entry, on the payload bytes x after the calls whose grants are os). The driver's
       frees after the last call take their one-call ROOM_cf from the interface's iface_room_np_tail. LIB_ROOM comes
       from a8's global bound (PresetCfnA.v lib_room_of_wf). NEW: the ledger room `cnt + Z.of_nat r * LCNT <=
       SIZE_MAX` for the same r calls. NEW: the error buffer's extent placed, xs_placed_cf ly S (a8's YG0ncf.v), at
       entry; the interface carries it across each call as the last conjunct of its pre and post.
   (3) FINV -> PINV (PresetCfnA.v section 3) with its ledger arguments cnt ran.
   (4) The harness is called THROUGH preset_lib_contract_x directly: the donor's lib-site leaf (lib/A/AD1m.v
       tfib_lib_site_x, the bridge from the driver's lib_pre to the interface) is inlined in the proof, so there is
       no LIB premise (a Theorem Labs lane's decision, 2026-10-28). Its side premises stay, as in the donor's lib/A/AD1p.v:
       MT_FREE, and RO_IN, now the inclusion of the image listing's relro range (pa_relro_lo / pa_relro_hi, the
       interface's read-only premise PRH_Base.arodata_okP) in the driver's in_ro_tfa.
   (5) NEW, the float state: a harness call returns in a float state fx' with frm_zero (fp_csr fx') (the
       interface's continuation), so the loop body is stated for every FPState fx with frm_zero (fp_csr fx), and the
       contract and the driver leaves are taken at every fx.
   (6) NEW: the no-refusal predicate NR on the input (the internal file closedwalk-plan.md section 2f) is a premise of the loop body,
       right after valid_fs; the outer premise NRB bridges it to the interface's PAYLOAD_ROOM for this payload.
   (7) The donor's MDI loses `Namei.fd_names_path (m_fds md) YI16.sink_path = false` (preset opens no file).
   (8) The interface's frame names ablocks_cf / afn_pre_cf / ajournal_cf are its abbreviations of YCbqG.v's journal
       layer at ARx := ARcf, so they are no parameters here; the loop's proof reads the content it uses through the
       three links of lib/A/PresetD1rAl.v, which it proves by unfolding.
   (9) The leaf shapes are lane CwSites' (lib/A/PresetD1sitesA.v at a working branch 19737933b33,
       copied byte for byte into this branch): free_site_cf, free_null_site_cf (over the same non-primary room
       iface_room_np), printf_first_cf, printf_next_cf and exit_leaf_cf, over ARcf at Hp = [].
   (10) NEW, memnorm (the interface's header item (8), a working branch 446222ec0601): the harness call needs
       YAkMemnorm.memnorm tfibsegs over the call configuration's FULL overlay, and its post keeps it. The loop takes it
       at its head (= the first harness call) as a premise of loop_L_cf_A, and carries it to each later call through
       the slot's post, the printf leaf's keep (CwSites), and the named premise H_memnorm_drv_A: AD1r's three runner
       segments between two calls (vp_run, br_run, l2_run) with memnorm at both ends. Owner of H_memnorm_drv_A:
       a Theorem Labs lane's closer YSRrMemnorm.SRr_msteps_inv (a working branch 60aa137eff2) with srr_inv_laws_memnorm.
   (11) NEW, the live real stack (the interface's header item (13), #102; a Theorem Labs lane's ruling 09:23Z): the slot pre's
       last conjunct is a Theorem Labs lane's YGcallStackUp.astack_up_x tfibsegs ly W (spZ regs) mem, UNGUARDED. The loop
       takes its part above the entry sp as an INVARIANT, a premise of loop_L_cf_A: astack_up_x at usp, every byte of
       [usp, ly_top) present. With the window [usp - 64 KiB, usp) of the call state S_L it gives the slot pre's
       conjunct at each call (lib/A/PresetStkUpA.v stk_up_at); the slot's journal, the printf leaf's presence keep and
       the frames of the runner segments carry it to the next call. The driver walk gives it at the loop head from
       main's entry (lib/A/PresetD1pA.v H_stackup_main_A).
   (12) The slot over the re-hiding relation (lib/A/PresetCfnA.v header item (14)): the harness call is taken through
       PCA.preset_lib_contract_xR at YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf, the form of the program slot
       preset_lib_contract_x_all, so its continuation's world step is wle' (the hidden set may grow inside RZ_cf),
       not wle.
   Dropped from the donor (preset's driver writes no file): every obligation on cgif's output file; this file names
   none of A_WB, A_TRAILER, A_PATH. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0n
YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI00 YI16 YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n
YG0d YCe5 YL02 YL04 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20
AD1v AD2h AD2f AD1w ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05 YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfTok YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base CfParamsPreset.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD1r AD25.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. NAMED PREMISE H_memnorm_drv_A (header item (10)): the driver keeps memnorm between two harness calls. These
   are its three runner segments from a harness return to the next harness call, vp_run, br_run and l2_run
   (lib/A/AD1r.v :333, :342, :351), each with memnorm on the full overlay at both ends. It is discharged by re-running
   AD1r's proofs of those lemmas with YSRrMemnorm.SRr_msteps_inv (a working branch) at
   P := YAkMemnorm.memnorm tfibsegs. It is not a law of every SRr fact (ruled 09:59Z: SRr W c Q -> SRr W c (Q /\ P) has
   no generic proof) and not an ARx law. *)
Definition H_memnorm_drv_A : Prop :=
forall fx : YK11.FPState,
(forall E (W : world tfibsegs) regs mem md,
  st_ok (fx := fx) tfibsegs E AD1r.S_LR (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom tfibsegs))) ->
  YAkMemnorm.memnorm tfibsegs mem ->
  SRr tfibsegs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom tfibsegs)) md)
    (fun W' c' => AD25.at_st AD1r.S_LR AD1r.S_VP E W mem md W' c' /\
       exists ms' md', c' = mkCfg ms' md' /\ YAkMemnorm.memnorm tfibsegs (ms_mem ms'))) /\
(forall E (W : world tfibsegs) regs mem md,
  st_ok (fx := fx) tfibsegs E AD1r.S_VPr (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 RA_EMIT) mem (seg_rom tfibsegs))) ->
  YAkMemnorm.memnorm tfibsegs mem ->
  SRr tfibsegs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 RA_EMIT) mem (seg_rom tfibsegs)) md)
    (fun W' c' => AD25.at_st AD1r.S_VPr AD1r.S_BR E W mem md W' c' /\
       exists ms' md', c' = mkCfg ms' md' /\ YAkMemnorm.memnorm tfibsegs (ms_mem ms'))) /\
(forall E (W : world tfibsegs) ms md,
  st_ok (fx := fx) tfibsegs E (add_cond AD1r.S_BR AD1r.cond_BRt) (restrict (w_H W) ms) ->
  YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => AD25.at_st AD1r.S_BR AD1r.S_L2 E W (ms_mem ms) md W' c' /\
       exists ms' md', c' = mkCfg ms' md' /\ YAkMemnorm.memnorm tfibsegs (ms_mem ms'))).

Section s.
Context {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg}.
Context {L : YP0b.ptable YPsym.asym} {PA : YC4aP.PAImg L}.
(* change (1): preset's allocator parameters are the only CfParams instance here *)
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Variable B : asyms.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Variable NR : ProcInput -> Prop.
Variable sm : list Z -> Z * Z.
Variable iface_room_np : astate -> Prop.
#[local] Notation ELV sp a0 p inp xw xd := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).

(* ---------------------------------------------------------------------- *)
(* 1. The loop body: lib/A/AD1w.v:208 loop_L_x with changes (1)-(3), (5)-(7) of the header. *)
Definition loop_L_cf_A : Prop :=
forall (fx : YK11.FPState), YK0o.frm_zero (@YK11.fp_csr fx) ->
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (E : YP0m.env)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb pq : sptr) (cap q : Z)
(j r : nat) (fs : Fs) (cnt ran : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
NR inp ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
(forall k, (k < K_M1)%nat -> ew E k = ew (ELV sp a0 p inp xw xd) k) -> ed E 2 = data ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E A_LEN) = dlen data ->
bv_unsigned (ew E 161) = sptr_addr B ly pb + 2 + config_len data ->
bv_unsigned (ew E 162) = payload_len data -> bv_unsigned (ew E 163) = (if payload_len data =? 0 then A_EMPTY_tfa else q) ->
bv_unsigned (ew E 164) = q -> bv_unsigned (ew E 166) = Z.of_nat r ->
st_ok tfibsegs E S_L (restrict (w_H W) ms) ->
(1 <= r)%nat -> (j + r = calls data)%nat ->
((payload_len data = 0 /\ q = 0 /\ blocks S = [(pb, cap)])
\/ (0 < payload_len data /\ blocks S = [(pb, cap); (pq, payload_len data)] /\ sptr_addr B ly pq = q)) ->
(0 < payload_len data -> blk (w_H W) (ms_mem ms) q (payload_len data) (payload data)) ->
frames S = [] -> qtight S -> iface_room_np S ->
(* the wild room for the r calls left (clause 4b of the kit's batch; lib/Reusable/YCbqGwild.v section 3, wild_room_run):
   each call's slot pre takes room for YCbqGwild.K_LLVMF fresh wild traces, and its post's journal stores at most that many *)
YCbqGwild.wild_room (as_universe B) [] (r * YCbqGwild.K_LLVMF) (st_depot S) ->
(* the interface's room over the j calls made (length os = j: the exit path's frees take the hull from it, A18's
   count over a run of at most 4 calls) *)
(exists os H0 hist, length os = j /\ PCA.iface_room_at sm (map (fun b : byte => bv_unsigned b) (payload data)) os H0 hist S) ->
xs_placed_cf ly S ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
(* #102 (no-DW interface): the count headroom the slot pre now asks, `cnt + LCNT < 2 ^ 62 - 2 ^ 30` (D2,
   PresetCfnA.v), for the r calls left; it implies the old `cnt + r * LCNT <= SIZE_MAX` *)
cnt + Z.of_nat r * PCA.LCNT < 2 ^ 62 - 2 ^ 30 -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap ->
((j = 0%nat /\ stdout_img (w_H W) (ms_mem ms)) \/ ((1 <= j)%nat /\ xst j (w_H W) (ms_mem ms))) ->
arodata_ok B (aview tfibsegs (w_H W) (ms_mem ms)) ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) cnt ran ->
(* header item (10): memnorm at the loop head, the first harness call (its ms_mem is the call's FULL overlay) *)
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
(* header item (11): the live real stack above the entry sp, the loop's invariant *)
YGcallStackUp.astack_up_x tfibsegs ly W (bv_unsigned sp) (ms_mem ms) ->
((forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) /\ m_fs md = fs /\ Fs.fs_sorted fs = true) ->
srealizes tfibsegs (mkCfg ms md) (loop_tgt (LS := LS) (payload data) (calls data) j r fs).

(* ---------------------------------------------------------------------- *)
(* 2. The premises of the loop theorem: the interface's remaining Section variables, the contract, the leaves. *)
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable PAYLOAD_ROOM : list byte -> Prop.

Definition loop_L_x_A_at : Prop :=
TfibSyms B -> AR_laws_cf tfibsegs B ->
(forall S m, mo_ok MT S m) ->
(forall a, @YC4aP.pa_relro_lo rc L PA <= a < @YC4aP.pa_relro_hi rc L PA -> in_ro_tfa a) ->
(forall inp a0 p data, NR inp -> in_argv inp = [a0; p] -> fs_lookup (in_fs inp) p = Some data -> PAYLOAD_ROOM (payload data)) ->
(forall fx : YK11.FPState, @PCA.preset_lib_contract_xR rc LS L PA ci sm iface_room_np B MT XM_LIB XN_LIB PAYLOAD_ROOM fx
  (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))) ->
(* #102 (no-DW interface): the slot pre's conjunct before the last, the instance universe's closure at the
   slot's context set (state-free; the closed top takes it from the instance's universe: a Theorem Labs lane's generator,
   a Theorem Labs lane's univcore) *)
@PRH_Base.prh_univ_closure PCA.preset_prh_img B ci PCA.iface_ctx0 ->
(* the slot's entry address: the listing's entry (the interface's A_LLVMF := pa_sigma of LLVMFuzzerTestOneInput) is the
   driver's call target, the A' entry 0x815e0 (lib/A/PAImg_prog.v A_entry_LLVMFuzzerTestOneInput at the instance) *)
@YC4aP.pa_sigma rc L PA YPsym.AS_LLVMFuzzerTestOneInput = 0x815e0 ->
(forall fx : YK11.FPState, printf_first_cf (fx := fx) B xst) -> (forall fx : YK11.FPState, printf_next_cf (fx := fx) B xst) ->
(* the exit path's frees after the last harness call, over drv_pre_cf without memnorm (PresetD1sitesA.v
   free_site_nomn_cf / free_null_site_nomn_cf): the exit path does not carry memnorm *)
(forall fx : YK11.FPState, free_site_nomn_cf (fx := fx) B iface_room_np) ->
(forall fx : YK11.FPState, free_null_site_nomn_cf (fx := fx) B iface_room_np) ->
(forall fx : YK11.FPState, exit_leaf_cf (fx := fx) B xst) ->
xst_frame_tfa xst ->
PCA.iface_room_np_tail iface_room_np ->
H_memnorm_drv_A ->
loop_L_cf_A.
End s.

(* ---------------------------------------------------------------------- *)
(* 3. THE STATEMENT. The donor's tfib_loop_L (lib/A/AD1r.v:1053) over ARcf / PINV / the program interface, closed. *)
Definition loop_L_x_A : Prop :=
forall (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg) (L : YP0b.ptable YPsym.asym) (PA : YC4aP.PAImg L)
(B : asyms) (xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (NR : ProcInput -> Prop)
(sm : list Z -> Z * Z) (iface_room_np : astate -> Prop)
(MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (PAYLOAD_ROOM : list byte -> Prop),
loop_L_x_A_at (rc := rc) (LS := LS) (ci := ci) (L := L) (PA := PA)
B xst NR sm iface_room_np MT XM_LIB XN_LIB PAYLOAD_ROOM.
