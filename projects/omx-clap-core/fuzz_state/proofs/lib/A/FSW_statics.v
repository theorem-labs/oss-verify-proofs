(* The entry symbolic state of an instrumented fs function that reads and writes fuzz/alloc.c's statics (fuzz_malloc,
   fuzz_free, fuzz_realloc): FSW_K's fss0T (the frame, the .got word of the ASan shadow base and the shadow cell, atom 32
   = SHADOW_OFF) plus the four 8-byte statics g_count, g_fail_at, g_live, g_peak as writable regions holding the extra
   atoms 33..36 = cnt, fail, live, peak (fs_glob's values). Without them the engine stops at the first `ld` of a static.
   ONE COPY (owner ruling 22:00Z): this file is the single writer of fss0TS / fsw_entryTS / fs_extraTS and of the
   read-back fs_glob_of_TS; it imports FSW_K and nothing in FSW_K imports it. fsw_entryTS is FSW_K.fsw_entryT_argsX at
   rs = fs_pstat_regions; fs_glob_of_TS is its inverse at a walk's end: from the final symbolic memory's four static
   chunks (found by address, fs_pstat_find) and their values, fs_glob of the final memory.
   fs_pstat_val is lib/A/AE3m.v val_mem_of_chunk8 (donor) with the chunk found by address instead of list index.
   Ported from: lib/A/FSW_K.v fss0T / fsw_entryT: the same proof, extended
   by the four static regions; the statics' bytes come from FSH_Base.fs_glob, their writability from fs.asan's RW load
   window (A/AB13.v tfib_rw_window, [0x9f000, 0x5fd000)). No rename. Reads the image cells tfib_D_GOT_... (0x9f6f0) and
   tfib_D_asan_shadow_memory_dynamic_address (0xa7f38) through the two cell equations of B, as fsw_entryT does.
   A kit file: no function's contract is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSPstat FSW_K.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AB13.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* one 8-byte static at g, writable, holding atom n; the four statics at xatom 0..3 (FSW_K's atom convention:
   T states reserve atom 32 for the shadow base, the walk's xs start at xatom 0 = 33) *)
Definition fs_pstat_region (g : Z) (n : nat) : YP09.region :=
  YP09.mkRegion None g (g + 8) g (g + 8) [YP09.mkChunk g (CVal 8 (SOff n 0))].
Definition fs_pstat_regions : list YP09.region :=
  [fs_pstat_region G_COUNT (xatom 0); fs_pstat_region G_FAIL (xatom 1); fs_pstat_region G_LIVE (xatom 2);
   fs_pstat_region G_PEAK (xatom 3)].
Definition fsTS_regions (f : Z) : list YP09.region := fsT_regions_args f fs_pstat_regions.
Definition fss0TS (pc f : Z) : sstate := fss0T_args pc f fs_pstat_regions [].
(* the statics' values, xatom 0..3 *)
Definition fs_pstat_xs (cnt fail live peak : Z) : list word := map (Z_to_bv 64) [cnt; fail; live; peak].
(* the entry env's extra atoms: 32 the shadow base, 33..36 the statics *)
Definition fs_extraTS (cnt fail live peak : Z) : list word := fs_extraT ++ fs_pstat_xs cnt fail live peak.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* the four static regions under an env whose xatom 0..3 are fs_glob's values *)
Lemma fs_pstat_regions_ok : forall (W : world tfibsegs) regs mem live peak cnt fail,
  fs_glob tfibsegs W mem live peak cnt fail ->
  Forall (region_ok tfibsegs (Ereg regs (fs_extraTS cnt fail live peak)) (mrestrict (w_H W) mem)) fs_pstat_regions.
Proof.
intros W regs mem live peak cnt fail GL.
pose proof GL as (G1 & G2 & G3 & G4 & GR).
set (E := Ereg regs (fs_extraTS cnt fail live peak)).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0))
  by (intros j Hj; subst E; apply ew_Ereg_extra).
assert (RS : forall g (j : nat) v, (1 <= j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> 0x9f000 <= g -> g + 8 <= 0x5fd000 -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  region_ok tfibsegs E (mrestrict (w_H W) mem) (fs_pstat_region g (32 + j))).
{ intros g j v Hj Hv Hr Hg1 Hg2 Hm.
  unfold region_ok, fs_pstat_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. unfold writable_at. apply AB13.tfib_rw_window. rewrite unsigned_lit_small by lia. lia.
  - constructor; [|constructor].
    exact (chunk_ok_val tfibsegs _ _ 0 g 8 (SOff (32 + j) 0) v
      ltac:(rewrite fsw_SOff0; etransitivity; [exact (EX j ltac:(lia)) | exact Hv]) ltac:(cbn [Z.of_N]; lia)
      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Hm)). }
unfold fs_pstat_regions, xatom.
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- apply (RS G_COUNT 1%nat cnt); [lia | reflexivity | lia | unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3].
- apply (RS G_FAIL 2%nat fail); [lia | reflexivity | lia | unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4].
- apply (RS G_LIVE 3%nat live); [lia | reflexivity | lia | unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1].
- apply (RS G_PEAK 4%nat peak); [lia | reflexivity | lia | unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2].
Qed.

(* the entry state: FSW_K.fsw_entryT_argsX at rs = fs_pstat_regions, gf = [], xs = the statics' values *)
Lemma fsw_entryTS : forall B STK f ly S U (W : world tfibsegs) regs mem md ch pc live peak cnt fail,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  afn_preU tfibsegs B STK ly S U W regs mem md ch -> 0 <= f <= STK ->
  regions_wf (fsTS_regions f) = true ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  st_ok tfibsegs (Ereg regs (fs_extraTS cnt fail live peak)) (fss0TS pc f)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros B STK f ly S U W regs mem md ch pc live peak cnt fail Hgot Hcell HPRE Hf Hwf GL.
pose proof (fsw_sp B STK ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (E2 : bv_unsigned (ew (Ereg regs (fs_extraTS cnt fail live peak)) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
apply (fsw_entryT_argsX B STK f ly S U W regs mem md ch pc fs_pstat_regions [] (fs_pstat_xs cnt fail live peak)
  Hgot Hcell HPRE Hf Hwf (fs_pstat_regions_ok W regs mem live peak cnt fail GL)).
all: first
  [ solve [exact I]
  | solve [ apply pairwise_disjoint_of_extents;
      unfold fsT_regions_args, fsT_regions, fs_pstat_regions, fs_got_region, fs_bcell_region, fstk, fs_pstat_region,
        extent_of_region;
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]; fold (fs_extraTS cnt fail live peak); rewrite E2;
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
        G_COUNT, G_FAIL, G_LIVE, G_PEAK;
      cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
      repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia] ] ].
Qed.
End e.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Read-back at a walk's end: the static chunks of the final symbolic memory give fs_glob of the final memory.       *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* the value of the first 8-byte chunk at absolute address g (a region with no base) *)
Fixpoint fs_pstat_find (rs : smem) (g : Z) : option sv :=
  match rs with
  | [] => None
  | r :: t =>
      match YP09.r_base r, List.find (fun c => YP09.c_off c =? g) (YP09.r_chunks r) with
      | None, Some (YP09.mkChunk _ (CVal n e)) => if (n =? 8)%N then Some e else fs_pstat_find t g
      | _, _ => fs_pstat_find t g
      end
  end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma fs_pstat_val : forall E (m : word -> option byte) rs g e v,
  Forall (region_ok tfibsegs E m) rs -> fs_pstat_find rs g = Some e ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m g 8 v.
Proof.
intros E m rs g e v HR. induction HR as [|r t Hr HR IH]; cbn [fs_pstat_find]; [discriminate|].
intros Hf He Hv.
destruct (YP09.r_base r) as [b|] eqn:Hb; [exact (IH Hf He Hv)|].
destruct (List.find (fun c => YP09.c_off c =? g) (YP09.r_chunks r)) as [[co cv]|] eqn:Hfd; [|exact (IH Hf He Hv)].
destruct cv as [n e'| | |]; try exact (IH Hf He Hv).
destruct (N.eqb_spec n 8) as [->|Hn]; [|exact (IH Hf He Hv)].
injection Hf as ->.
apply find_some in Hfd as [Hin Hoff]. apply Z.eqb_eq in Hoff. cbn [YP09.c_off] in Hoff. subst co.
destruct Hr as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck.
rewrite <- (Z.add_0_l g). apply (val_of_chunk_ok tfibsegs E m 0 g 8 e v Hck He); cbn; lia.
Qed.

(* fs_glob from the final symbolic memory: each static's chunk, its value, and alloc.c's ranges *)
Lemma fs_glob_of_TS : forall E (W : world tfibsegs) mem rs live peak cnt fail el ep ec ef,
  mem_ok tfibsegs E (mrestrict (w_H W) mem) rs ->
  fs_pstat_find rs G_LIVE = Some el -> fs_pstat_find rs G_PEAK = Some ep ->
  fs_pstat_find rs G_COUNT = Some ec -> fs_pstat_find rs G_FAIL = Some ef ->
  sv_denot E el = Z_to_bv 64 live -> sv_denot E ep = Z_to_bv 64 peak ->
  sv_denot E ec = Z_to_bv 64 cnt -> sv_denot E ef = Z_to_bv 64 fail ->
  0 <= live <= peak -> peak < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 ->
  fs_glob tfibsegs W mem live peak cnt fail.
Proof.
intros E W mem rs live peak cnt fail el ep ec ef (_ & HR & _) Fl Fp Fc Ff El Ep Ec Ef Hl Hp Hc Hf.
split; [exact (fs_pstat_val E _ rs G_LIVE el live HR Fl El ltac:(lia))|].
split; [exact (fs_pstat_val E _ rs G_PEAK ep peak HR Fp Ep ltac:(lia))|].
split; [exact (fs_pstat_val E _ rs G_COUNT ec cnt HR Fc Ec Hc)|].
split; [exact (fs_pstat_val E _ rs G_FAIL ef fail HR Ff Ef Hf)|].
lia.
Qed.
End b.

(* the four statics are image bytes (fs.asan's last RW load segment covers each 8-byte range): the third arm of the
   FP-keyed journal composition (`inFP FP a /\ in_img tfibsegs a`) for a callee at FS_PSTAT_FP *)
Lemma fs_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
    (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) FS_PSTAT_FP = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. cbv beta in H.
apply existsb_exists in H as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
