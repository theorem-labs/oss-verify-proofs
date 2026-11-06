(* fs program part, lane ENTRY, IMAGE B (fs.asan-ubsan, pinned sha256 5ac5ce0954f8...): the ROOM AT THE TOP of a live
   ASan block. AR_blocks_law (Reusable/YG0d.v) bounds a block by `p + req_size n <= alloc_ceiling`, one byte too weak
   for the 8-byte word reads of musl's strlen / bcmp over the block's last byte; fe_block_room closes the gap from the
   chunk geometry, for every live block:
   - a PRIMARY chunk sits at region_base ly c + x with x + class_size c <= rg_alloc_user (reg S c) <= kFreeArrayOffset
     (0xE0000000, YG00.v), and a region is 2 ^ 32 wide and ends below ASAN_CEIL (YG0s.v region_in_prim), so the chunk
     ends at least 2 ^ 32 - 0xE0000000 bytes below the ceiling;
   - a SECONDARY chunk's mapping holds needed_size = rounded_size n + 2 * rz_size n user-and-redzone bytes, and
     rz_size >= 16 (YG0a.v rz_size_bounds), so the user bytes end at least 16 bytes below the end of the chunk's extent,
     which AR bounds by ASAN_CEIL (YG0s.v cfacts).
   The statement and proof are image-generic (the allocator model of the shared core) over B's tfibsegs.
   rule 24: proves function LLVMFuzzerTestOneInput (shared kit of the entry walk's segments S3 / S5 / S6; reuse search:
   proof-index LLVMFuzzerTestOneInput, ported from a working branch 08ad70da3bf).
   Ported from: lib/A/FSW_entry_ar.v (a working branch 0d34d65d2b7), A's names, AB1v replaced by B's YB1v.
   RELOC-B hypotheses: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0s YG0n YG0d YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the user bytes of a SECONDARY chunk end at least 16 bytes below its extent: the mapping holds a redzone on each
   side (needed_size n = needed_primary n + rz_size n, YG00.v) *)
Lemma fe_sec_slack : forall n, 0 <= n -> from_primary n = false ->
  rz_size n + req_size n + 8 <= sec_map_size n - kPage.
Proof.
intros n Hn Hfp.
pose proof (rz_size_bounds n) as [[R1 R2] _].
pose proof (needed_primary_bounds n Hn) as (P1 & _ & _).
unfold sec_map_size, needed_size. rewrite Hfp.
pose proof (round_up_ge (needed_primary n + rz_size n) kPage ltac:(unfold kPage; lia)) as [[Q1 _] _].
unfold kPage in *. lia.
Qed.

(* the room a live block has at the top: enough for the 8-byte word that holds its last byte *)
Lemma fe_block_room : forall ly S (W : world tfibsegs) mem md p n,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n + 8 <= alloc_ceiling.
Proof.
intros ly S W mem md p n HAR Hin.
pose proof (proj1 HAR) as M. pose proof (am_layout _ _ _ _ M) as LO.
apply In_ablocks in Hin as (k & Hk & _ & Hu & Hr).
pose proof (chunk_facts B ly S _ k M Hk) as CF.
pose proof CF as (_ & Hceil & _ & Huser & Hrz & _ & Hreq & Hext & Harm).
rewrite <- Hu, <- Hr, Huser.
destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; [destruct Harm | | | destruct Harm].
- (* primary: the chunk ends below the free array, which is 2 ^ 32 - 0xE0000000 under the region's top *)
  cbv zeta in Harm.
  destruct Harm as (Hc & _ & _ & Hext' & Hbase & Hx & _ & Hxa & Hau & Hmu).
  pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (_ & _ & _ & _ & Hreg).
  unfold ASAN_CEIL in *. unfold kFreeArrayOffset in Hmu. rewrite Hbase, Hext' in *. lia.
- (* secondary: the second redzone is the slack *)
  cbv zeta in Harm. destruct Harm as (_ & Hfp & _ & Hext' & _ & _ & _).
  pose proof (fe_sec_slack (ck_req k) ltac:(lia) Hfp) as Hs.
  unfold ck_rz in *. unfold ASAN_CEIL in Hceil. rewrite Hext' in *. lia.
Qed.
End a.
