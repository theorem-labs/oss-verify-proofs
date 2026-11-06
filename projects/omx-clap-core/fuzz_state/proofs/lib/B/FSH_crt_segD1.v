(* check_round_trip 0x81b9c (fuzz_state.c:278-314 with round_trip_document fs.c:229-264 inlined), fs.asan-ubsan (image
   tfibsegs = lib/B/YB1v.v, the pinned fuzz_state.asan-ubsan sha256
   5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204): the B twin of the ASan walk of lib/B/FSH_Fn_crt.v
   check_round_trip_spec, LANE D1 = segments 30-33, from the return of pj_get_str at 0x823bc (0x823c0, crt_INV_82268)
   to the return of fuzz_free (file) at 0x82404 (0x82408, crt_INV_822ac, published in lib/B/FSH_crt_base.v), with the
   class-3 fake frame live (own = [(3, pos)]).

   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 82a1d1bf3a6 lib/A/FSH_crt_segD1.v)
   Port source: a working branch 82a1d1bf3a6 proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segD1.v, itself
   PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/
   check_round_trip_stdefs.v St17 :521 / St18 :535 and check_round_trip_sd16.v crt16_runB :541 / crt16_runA :392, with
   check_round_trip_sd17.v and check_round_trip_sd18.v for the two fuzz_free steps (the checker's CONFIRM for this walk
   is on the lane head (internal path), role check, 2026-10-29
   04:3xZ: the hit's Require closure is 334 files with 0 Admitted / Axiom / Parameter). Same Definition / Lemma names
   and statement shapes as the A file, over image B; every pc, return address, register and slot fact RE-MEASURED on B
   (capstone over the pinned fs.asan-ubsan, (internal path)) and mapped from A by
   instruction meaning (crt.A2B.tsv: every pc of this range is an `equal` row except A 0x8226c / 0x8227c, mapped by
   meaning below). The shared interface is lib/B/FSH_crt_base.v / lib/B/FSH_crt_site.v; the kit steps are lib/B
   FSW_K.v / FSW_rres.v / FSW_rd.v, used and not copied. A new file: no licence lines.

   A name -> A pc -> B pc (names keep their A form, content is B's):
     crtD1_ss30 / crtD1_sc30        0x82268 -> 0x823c0 (return of pj_get_str), run to the decode 0x84c4c, ra 0x823cc
     crtD1_ss31_base / crtD1_ss31 /
       crtD1_sc31 / crtD1_ss31z /
       crtD1_sb31z / crtD1_ss31zc /
       crtD1_sc31z                  0x82274 -> 0x823cc (return of the second decode), bcmp ra 0x82298 -> 0x823f4,
                                    `beqz s4` 0x82284 -> 0x823e0, fuzz_free (got) ra 0x822a4 -> 0x82400
     crtD1_ss32 / crtD1_sb32 /
       crtD1_ss32c / crtD1_sc32     0x82298 -> 0x823f4 (return of bcmp), fuzz_free ra 0x822a4 -> 0x82400
     crtD1_ss33 / crtD1_sc33        0x822a4 -> 0x82400 (return of fuzz_free (got)), fuzz_free ra 0x822ac -> 0x82408
     crtD1_ssout                    0x822ac -> 0x82408 (return of fuzz_free (file)) = lib/B/FSH_crt_segD.v's crt_ss34

   The four calls of this lane (MEASURED on fs.asan-ubsan; A in brackets; return address in brackets):
     30  0x823c0..0x823c8  preset_base64_decode (z, &n)       [0x823cc]  `beqz a0` 0x823c0 decided by z <> 0; a1 = &n
                            is read from the s1 slot 0x28 (0x823c4 `ld a1, 0x28(s1)`, crt_cs1's SOff 47 0x1a0)
                            [A 0x8226c `mv a1, s11`]
     31  0x823cc..0x823f0  bcmp (got, bd, len)                [0x823f4]  guarded by `bne a0, s4` (n = |bs|) at 0x823dc
                            and SKIPPED when |bs| = 0 (`beqz s4` 0x823e0 -> 0x823f8); the length cell is read through
                            the slot (0x823d4 `ld a0, 0x28(s1)`, 0x823d8 `ld a0, 0(a0)`) [A 0x8227c `ld a0, 0(s11)`]
     32  0x823f4..0x823fc  fuzz_free (got)                    [0x82400]
     33  0x82400..0x82404  fuzz_free (file)                   [0x82408]
   The trap arms this lane must show unreachable: `__asan_handle_no_return` 0x824e4 and `abort` 0x824e8, reached from
   the four guards at 0x823c0 (z <> 0, crt_INV_82268), 0x823cc (the decode's got <> 0, its success post), 0x823dc (the
   length cell at F + 0x1a0 holding |bs|, the decode's val_mem post) and 0x823f4 (bcmp = 0 on equal bytes,
   FsRt.fr_bcmp). No edge from this lane's range reaches the UBSan trap 0x82620 or the `__asan_report_*` arms
   0x82624..0x8266c (lib/B/FSH_crt_segD.v's MEASURED branch-target scan: they are reached only from segments 5 and 7).

   B's register allocation differs from A's in this lane: &n = F + 0x1a0 lives in the s1 slot 0x28 (A: s11), so the
   seg-30 run hands the decode a1 = SOff 47 0x1a0 (A: s11's atom 27), and the seg-31 start state re-seats NO register
   (A re-seats s11 on the frame atom); the inner invariants' register heads are B's crt_INV_822ac's (FSH_crt_segD1_inv.v).

   R1 hold: the decode call at 0x823c8 takes decode_spec_ff with a Theorem Labs lane's kept-buffer premise
   `wsrc_kept ly S U W mem 0 z (zs ++ [0])`; it is discharged from crt_INV_82268's own live blocks (the string z is a
   block of the parsed document's list Dback, rd_blocks_ok). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YG0s YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_frame
FSW_rd FSW_strkit FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base
FSH_crt_site.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE2k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct
  check_round_trip_stages_b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition D1_FUEL : N := 200%N.

(* ================= the lane's boundary states and straight-line runs (MEASURED by the engine over the lane's decode
   table lib/B/FSW_crt_tbl.v on the pinned fs.asan-ubsan; every lemma below is closed by vm_compute) =================
   Each state is the base's crt_ss_ret at the call's return address with ATOM FACTS added (YP06.add_atom) for what the
   boundary invariant and the callee posts give, so the engine decides this lane's four guards itself:
     atom 10 in [4096, 2 ^ 47)  a0 is a live heap pointer, so `beqz a0` at 0x823c0 / 0x823cc is not taken
                                (crt_INV_82268's z <> 0 with cstr_ok's 4096 <= z; the decode's got <> 0 with its
                                 4096 + HEAD <= got);
     atom 20 >= 1 or = 0        s4 = |bs|, which decides `beqz s4` at 0x823e0 (the empty-body arm skips bcmp);
     atom 10 = 0                bcmp returned 0, so `bnez a0` at 0x823f4 is not taken.
   `bne a0, s4` at 0x823dc needs no fact: the decode wrote |bs| into the length cell, so both sides are atom 20.
   The frame chunk list at 0x823cc carries that cell (the `n` of round_trip_document at F + 0x1a0, which the decode
   writes): crtD1_csF31, as lib/B/FSH_crt_segD.v's crt_csF31. B reads the cell through the s1 slot 0x28 (crt_cs1's
   SOff 47 0x1a0: 0x823d4 `ld a0, 0x28(s1)`, 0x823d8 `ld a0, 0(a0)`), so no register is re-seated (A: s11). *)
Definition crtD1_fptr : afact := mkAF 4096 (2 ^ 47) 0.
Definition crtD1_fzero : afact := mkAF 0 0 0.
Definition crtD1_csF31 : list YP09.chunk := YP09.mkChunk 0x1a0 (CVal 8 (SOff 20 0)) :: crt_csF.

(* ---- segment 30: 0x823c0 .. the decode's entry 0x84c4c (ra 0x823cc), a1 = &n = F + 0x1a0, read from the s1 slot
   0x28 (0x823c4 `ld a1, 0x28(s1)`), so a1 is the slot chunk's SOff 47 0x1a0 (A: s11 = atom 27) ---- *)
Definition crtD1_ss30 : sstate := add_atom (crt_ss_ret 0x823c0 crt_cs1 crt_csF) 10 crtD1_fptr.
Definition crtD1_sc30 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl D1_FUEL A_preset_base64_decode crtD1_ss30).
Lemma crtD1_run30 :
  sym_run_toN tfibsegs crt_tbl D1_FUEL A_preset_base64_decode crtD1_ss30 = (crtD1_sc30, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1_sc30_regs :
  ss_pc crtD1_sc30 = A_preset_base64_decode /\
  map (fun r => sr_get (ss_regs crtD1_sc30) r) [1; 10; 11; 2; 3; 4; 8]%bv =
  [SLit 0x823cc; SOff 10 0; SOff 47 0x1a0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 8 0] /\
  nth_error (ss_mem crtD1_sc30) 0 = Some crt_s0_region /\ ss_resv crtD1_sc30 = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ---- segment 31, body arm (|bs| >= 1): 0x823cc .. the bcmp thunk 0x426d8 (ra 0x823f4), a0 = got (atom 10),
   a1 = bd (atom 21), a2 = len (atom 20).
   The start state is the shared crt_ss2 shape (the saved words and the s1 slots) PLUS the frame as a READ-ONLY
   region carrying the length cell, because the stretch reads that cell (0x823d8 `ld a0, 0(a0)`, a0 = the slot 0x28's
   F + 0x1a0) and writes nothing: with an empty write window [0, 0) the run's frame still keeps every byte below
   alloc_ceiling, which is what FSH_crt_site.crt_call_core asks (`same_below`). Every register is its own atom: the
   cell's address comes from the slot region, so no register is re-seated (A re-seats s11). ---- *)
Definition crtD1_fr_ro : YP09.region := YP09.mkRegion (Some 47%nat) 0 (fs_frame_bytes 3) 0 0 crtD1_csF31.
Definition crtD1_ss31_base : sstate :=
  mkSS 0x823cc sr_atoms
    [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro] None
    (mkFacts ((8%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: crt_ret_facts) [] []).
Definition crtD1_ss31 : sstate := add_atom (add_atom crtD1_ss31_base 10 crtD1_fptr) 20 (mkAF 1 (2 ^ 32) 0).
Definition crtD1_sc31 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl D1_FUEL PC_bcmp crtD1_ss31).
Lemma crtD1_run31 : sym_run_toN tfibsegs crt_tbl D1_FUEL PC_bcmp crtD1_ss31 = (crtD1_sc31, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1_sc31_regs :
  ss_pc crtD1_sc31 = PC_bcmp /\
  map (fun r => sr_get (ss_regs crtD1_sc31) r) [1; 10; 11; 12; 2; 3; 4; 23]%bv =
  [SLit 0x823f4; SOff 10 0; SOff 21 0; SOff 20 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 10 0] /\
  ss_resv crtD1_sc31 = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ---- segment 31, empty-body arm (|bs| = 0): 0x823cc .. fuzz_free's entry 0x82dbc (ra 0x82400), bcmp skipped by
   `beqz s4` at 0x823e0. An atom fact lets the engine decide a branch NOT taken; a branch that IS taken is decided by
   a condition on the state (YP06.add_cond, discharged at the call site with st_ok_add_cond from |bs| = 0). ---- *)
Definition crtD1_ss31z : sstate := add_atom crtD1_ss31_base 10 crtD1_fptr.
Definition crtD1_sb31z : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl D1_FUEL crtD1_ss31z).
Lemma crtD1_br31z : sym_runN tfibsegs crt_tbl D1_FUEL crtD1_ss31z
  = (crtD1_sb31z, RS_stopped (SR_branch BC_EQ (SOff 20 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtD1_ss31zc : sstate := add_cond crtD1_sb31z (mkAC BC_EQ (SOff 20 0) (SLit 0)).
Definition crtD1_sc31z : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl D1_FUEL A_fuzz_free crtD1_ss31zc).
Lemma crtD1_run31z : sym_run_toN tfibsegs crt_tbl D1_FUEL A_fuzz_free crtD1_ss31zc = (crtD1_sc31z, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1_sc31z_regs :
  ss_pc crtD1_sc31z = A_fuzz_free /\
  map (fun r => sr_get (ss_regs crtD1_sc31z) r) [1; 10; 2; 3; 4; 8]%bv =
  [SLit 0x82400; SOff 10 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 8 0] /\
  nth_error (ss_mem crtD1_sc31z) 0 = Some crt_s0_region /\ ss_resv crtD1_sc31z = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ---- segment 32: 0x823f4 (bcmp returned 0, so `bnez a0` is NOT taken) .. fuzz_free's entry (ra 0x82400),
   a0 = s7 = got (atom 23) ---- *)
Definition crtD1_ss32 : sstate := crt_ss_ret 0x823f4 crt_cs1 crt_csF.
Definition crtD1_sb32 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl D1_FUEL crtD1_ss32).
Lemma crtD1_br32 : sym_runN tfibsegs crt_tbl D1_FUEL crtD1_ss32
  = (crtD1_sb32, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtD1_ss32c : sstate := add_cond crtD1_sb32 (mkAC BC_EQ (SOff 10 0) (SLit 0)).
Definition crtD1_sc32 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl D1_FUEL A_fuzz_free crtD1_ss32c).
Lemma crtD1_run32 : sym_run_toN tfibsegs crt_tbl D1_FUEL A_fuzz_free crtD1_ss32c = (crtD1_sc32, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1_sc32_regs :
  ss_pc crtD1_sc32 = A_fuzz_free /\
  map (fun r => sr_get (ss_regs crtD1_sc32) r) [1; 10; 2; 3; 4; 8]%bv =
  [SLit 0x82400; SOff 23 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 8 0] /\
  nth_error (ss_mem crtD1_sc32) 0 = Some crt_s0_region /\ ss_resv crtD1_sc32 = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ---- segment 33: 0x82400 .. fuzz_free's entry (ra 0x82408), a0 = s6 = file (atom 22) ---- *)
Definition crtD1_ss33 : sstate := crt_ss_ret 0x82400 crt_cs1 crt_csF.
Definition crtD1_sc33 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl D1_FUEL A_fuzz_free crtD1_ss33).
Lemma crtD1_run33 : sym_run_toN tfibsegs crt_tbl D1_FUEL A_fuzz_free crtD1_ss33 = (crtD1_sc33, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1_sc33_regs :
  ss_pc crtD1_sc33 = A_fuzz_free /\
  map (fun r => sr_get (ss_regs crtD1_sc33) r) [1; 10; 2; 3; 4; 8]%bv =
  [SLit 0x82408; SOff 22 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 8 0] /\
  nth_error (ss_mem crtD1_sc33) 0 = Some crt_s0_region /\ ss_resv crtD1_sc33 = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ---- the lane's exit state: the base's after-call state at 0x82408 with the base's frame chunks, i.e. exactly
   lib/B/FSH_crt_segD.v's crt_ss34, which lane D2 starts from ---- *)
Definition crtD1_ssout : sstate := crt_ss_ret 0x82408 crt_cs1 crt_csF.

(* ================= the state at the start of segment 31 =================
   The boundary state at 0x823cc is the base's crt_ss_ret with the flag chunk only: the length cell F + 0x1a0 is
   INSIDE the decode's footprint, so crt_after_call cannot carry it across the call, and the cell's value is read
   back from the decode's own post (crtD1_INV_82274's val_mem). These two steps put it into the symbolic state:
   crtD1_add_ncell adds the chunk to the frame region, crtD1_ss31_ok then drops to the read-only three-region shape
   (B: no register is re-seated, the cell's address is the s1 slot 0x28's chunk). ================= *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

(* the frame region of a boundary state, with the length cell added: region_ok gains one chunk_ok (the invariant's
   val_mem), the extents do not move, so regions_wf and the pairwise disjointness are the old ones *)
Lemma crtD1_add_ncell : forall cx E (W : world tfibsegs) ms r len,
  crt_E cx E -> 0 <= crt_F cx < 2 ^ 64 -> ew E 20 = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (crt_F cx + 0x1a0) 8 len ->
  st_ok tfibsegs E (crt_ss_ret r crt_cs1 crt_csF) (restrict (w_H W) ms) ->
  st_ok tfibsegs E (crt_ss_ret r crt_cs1 crtD1_csF31) (restrict (w_H W) ms).
Proof.
intros cx E W ms r len HE HF E20 Hlen Hval HS.
assert (E47 : bv_unsigned (ew E 47) = crt_F cx)
  by (rewrite (crt_E_F cx E HE), Z_to_bv_unsigned, bv_wrap_small
        by (change (bv_modulus 64) with (2 ^ 64); lia); reflexivity).
destruct HS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
split; [exact A6|]. split; [exact A7|]. split; [|exact A9].
(* the memory: the same four regions, the third with one more chunk *)
unfold crt_ss_ret, fss_ret_s0_args, fss_ret_s0_regs, crt_ret_regions in A8 |- *.
cbn [ss_mem] in A8 |- *.
destruct A8 as (Hwf & Hok & Hpd).
assert (HCH : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 47))
    (YP09.mkChunk 0x1a0 (CVal 8 (SOff 20 0)))).
{ apply (chunk_ok_val tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 47)) 0x1a0 8 (SOff 20 0) len).
  - rewrite fsw_SOff0. exact E20.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - cbn [N.to_nat]. rewrite E47. exact Hval. }
split.
- clear - Hwf. vm_compute. reflexivity.
- split.
  + apply Forall_cons_iff in Hok as (Ok0 & Hok). apply Forall_cons_iff in Hok as (Ok1 & Hok).
    apply Forall_cons_iff in Hok as (Ok2 & Hok).
    apply Forall_cons; [exact Ok0|]. apply Forall_cons; [exact Ok1|]. apply Forall_cons; [|exact Hok].
    destruct Ok2 as (O1 & O2 & O3 & O4).
    unfold crt_frame_region in O1, O2, O3, O4 |- *.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in O1, O2, O3, O4 |- *.
    split; [exact O1|]. split; [exact O2|]. split; [exact O3|].
    unfold crtD1_csF31. apply Forall_cons; [exact HCH | exact O4].
  + cbn [pairwise_disjoint all_disjoint] in Hpd |- *.
    destruct Hpd as (D1 & D2 & D3 & D4).
    unfold crt_frame_region, YP09.extent_disjoint in D1, D2, D3 |- *.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi] in D1, D2, D3 |- *.
    split; [exact D1|]. split; [exact D2|]. split; [exact D3 | exact D4].
Qed.

(* the three-region start state of segment 31: the frame becomes READ-ONLY (its write window empty, so the run's
   frame keeps every byte below alloc_ceiling, which crt_call_core asks as `same_below`) and the shadow region is
   dropped (the stretch does not touch it). B re-seats no register: the run reads the length cell's address from the
   s1 slot 0x28 (0x823d4), which the slot region carries, so A's s11 premises (ew E 27 = F + 0x1a0 and its range) have
   no B counterpart and are not taken *)
Lemma crtD1_ss31_ok : forall cx E (W : world tfibsegs) ms len,
  crt_E cx E -> 0 <= crt_F cx < 2 ^ 64 -> ew E 20 = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (crt_F cx + 0x1a0) 8 len ->
  st_ok tfibsegs E (crt_ss_ret 0x823cc crt_cs1 crt_csF) (restrict (w_H W) ms) ->
  st_ok tfibsegs E crtD1_ss31_base (restrict (w_H W) ms).
Proof.
intros cx E W ms len HE HF E20 Hlen Hval HS.
pose proof (crtD1_add_ncell cx E W ms 0x823cc len HE HF E20 Hlen Hval HS) as HS1.
assert (HSUB : submem [crt_s0_region; crt_slot_region crt_cs1; crtD1_fr_ro]
    (ss_mem (crt_ss_ret 0x823cc crt_cs1 crtD1_csF31))).
{ cbn [ss_mem crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions].
  apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [|apply submem_nil].
  unfold subregion, crtD1_fr_ro, crt_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc. exact Hc. }
exact (st_ok_submem tfibsegs E _ _ _ HS1 HSUB ltac:(vm_compute; reflexivity)).
Qed.

(* fs's four allocator statics are image bytes below 0x5fd000 (B: g_fail_at 0xa41c0, g_live 0x5daac0, g_peak
   0x5daae0, g_count 0x5dab00, lib/B/FSH_Base.v), so a step that keeps every byte there keeps fs_glob *)
Lemma crtD1_glob_keep : forall (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, 0 <= a < 0x5fd000 -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (HB4 : 0 <= G_FAIL /\ G_FAIL + 8 <= 0x5fd000 /\ 0 <= G_LIVE /\ G_LIVE + 8 <= 0x5fd000 /\
  0 <= G_PEAK /\ G_PEAK + 8 <= 0x5fd000 /\ 0 <= G_COUNT /\ G_COUNT + 8 <= 0x5fd000)
  by (unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT; repeat split; vm_compute; discriminate).
assert (VB : forall g v, 0 <= g -> g + 8 <= 0x5fd000 ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg0 Hg1 Hv kk Hkk.
  assert (HA : 0 <= g + Z.of_nat kk < 0x5fd000) by lia.
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' (g + Z.of_nat kk) (Hk (g + Z.of_nat kk) HA)).
  exact (Hv kk Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | lia | exact G1]|]. split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|]. split; [apply VB; [lia | lia | exact G4]|]. exact R.
Qed.
End w.
