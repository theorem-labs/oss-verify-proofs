(* check_no_overread 0x80b20 (fuzz_manifest.c:176-189), 165 instructions: the walk's context (check_no_overread_spec's
   premises at CTX_check_no_overread), its post, and the concrete state at each point the walk resumes from. The segment
   lemmas (lib/A/FMW_cno_*.v) each prove: from the state at one resume point, given the post holds from the next resume
   point's state, the post holds. FMW_cno.v chains them.

   Resume points (return addresses of the calls; 0x52dbc malloc, 0x51a68 __asan_memcpy, 0x51f04 __asan_memset,
   0x81be4 lv2_locate_manifest_names, 0x52db8 free):
     P1 0x80b80  after malloc (un + 18) -> u1        Q1 0x80b9c  after memcpy (u1, up, un) or its skip (un = 0)
     R1 0x80bc4  after memset (u1 + un + 1, 'a', 16)  P2 0x80bec  after malloc (tn + 18) -> t1
     Q2 0x80c08  after memcpy (t1, tp, tn) / skip     R2 0x80c30  after memset (t1 + tn + 1, 'a', 16)
     P3 0x80c54  after malloc (un + 18) -> u2         Q3 0x80c70  after memcpy (u2, up, un) / skip
     R3 0x80c88  after memset (u2 + un, 0, 17)        P4 0x80ca4  after malloc (tn + 18) -> t2
     Q4 0x80cc0  after memcpy (t2, tp, tn) / skip     R4 0x80cd8  after memset (t2 + tn, 0, 17)
     N1 0x80cf8  after names (t1, u1)                 N2 0x80d08  after names (t2, u2)
     F1 0x80d14  after free (u1)   F2 0x80d1c  after free (t1)   F3 0x80d24  after free (u2); then the tail free (t2). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- addresses ---- *)
Definition CNO_P1 : Z := 0x80b80.  Definition CNO_Q1 : Z := 0x80b9c.  Definition CNO_R1 : Z := 0x80bc4.
Definition CNO_P2 : Z := 0x80bec.  Definition CNO_Q2 : Z := 0x80c08.  Definition CNO_R2 : Z := 0x80c30.
Definition CNO_P3 : Z := 0x80c54.  Definition CNO_Q3 : Z := 0x80c70.  Definition CNO_R3 : Z := 0x80c88.
Definition CNO_P4 : Z := 0x80ca4.  Definition CNO_Q4 : Z := 0x80cc0.  Definition CNO_R4 : Z := 0x80cd8.
Definition CNO_N1 : Z := 0x80cf8.  Definition CNO_N2 : Z := 0x80d08.
Definition CNO_F1 : Z := 0x80d14.  Definition CNO_F2 : Z := 0x80d1c.  Definition CNO_F3 : Z := 0x80d24.
Definition PC_malloc : Z := 0x52dbc.  Definition PC_free : Z := 0x52db8.
Definition PC_memcpy : Z := 0x51a68.  Definition PC_memset : Z := 0x51f04.
Definition CNO_FRAME : Z := 96.
(* the saved registers (ra, s0..s9) and their slots above sp after the prologue *)
Definition cno_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25].
Definition cno_saved_offs : list Z := [88; 80; 72; 64; 56; 48; 40; 32; 24; 16; 8].

(* ---- the code table of the function ---- *)
Definition fmw_tbl_cno : ctable := Eval vm_compute in build_table tfibsegs A_check_no_overread 165 TEmpty.
Lemma fmw_tbl_cno_ok : table_ok tfibsegs fmw_tbl_cno.
Proof.
assert (E : fmw_tbl_cno = build_table tfibsegs A_check_no_overread 165 TEmpty) by (vm_cast_no_check (eq_refl fmw_tbl_cno)).
rewrite E. apply build_table_ok0. unfold A_check_no_overread. lia.
Qed.

Record cnx := mkNX {
  nx_ly : alayout; nx_S : astate; nx_W : world tfibsegs; nx_regs : bvmap 5 word; nx_mem : word -> option byte;
  nx_md : Model; nx_up : Z; nx_tp : Z; nx_ub : list Z; nx_tb : list Z; nx_live : Z; nx_peak : Z; nx_cnt : Z }.
Definition nx_sp0 (cx : cnx) : Z := spZ (nx_regs cx).
Definition nx_un (cx : cnx) : Z := Z.of_nat (length (nx_ub cx)).
Definition nx_tn (cx : cnx) : Z := Z.of_nat (length (nx_tb cx)).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* a source window's home: empty, or inside a block live at the entry (check_no_overread_spec, hdesign 0caf3fb9019) *)
Definition cno_home (ly : alayout) (S : astate) (p : Z) (l : list Z) : Prop :=
  l = [] \/ exists b m, In (b, m) (ablocks B ly S) /\ b <= p /\ p + Z.of_nat (length l) <= b + m.

(* check_no_overread_spec's premises at CTX_check_no_overread (so ch = [] and ra = 0x809e0), fail = SIZE_MAX (quiet) *)
Definition cno_base (cx : cnx) : Prop :=
  fpre tfibsegs B STK_check_no_overread (nx_ly cx) (nx_S cx) (nx_W cx) (nx_regs cx) (nx_mem cx) (nx_md cx) [] /\
  raZ (nx_regs cx) = 0x809e0 /\
  getr (nx_regs cx) 10 = w64 (nx_up cx) /\ getr (nx_regs cx) 11 = w64 (nx_un cx) /\
  getr (nx_regs cx) 12 = w64 (nx_tp cx) /\ getr (nx_regs cx) 13 = w64 (nx_tn cx) /\
  src_rd tfibsegs (nx_W cx) (nx_mem cx) (nx_up cx) (nx_ub cx) /\ src_rd tfibsegs (nx_W cx) (nx_mem cx) (nx_tp cx) (nx_tb cx) /\
  Forall (fun c => c <> 0) (nx_ub cx) /\ Forall (fun c => c <> 0) (nx_tb cx) /\
  cno_home (nx_ly cx) (nx_S cx) (nx_up cx) (nx_ub cx) /\ cno_home (nx_ly cx) (nx_S cx) (nx_tp cx) (nx_tb cx) /\
  (length (nx_ub cx) <= 255)%nat /\ nx_tn cx <= MANIFEST_MAX /\
  fm_glob tfibsegs (nx_W cx) (nx_mem cx) (nx_live cx) (nx_peak cx) (nx_cnt cx) SIZE_MAXZ /\
  quiet (nx_cnt cx) SIZE_MAXZ 2 /\ nx_live cx + nx_un cx + 3 < 2 ^ 33 /\
  st_nev (nx_S cx) + EV_check_no_overread <= EV_MAX /\ blocks_bytes (nx_S cx) + LIVE_check_no_overread <= LIVE_MAX.

Definition cno_post (cx : cnx) : world tfibsegs -> config -> Prop :=
  fpost tfibsegs B STK_check_no_overread FM_PSTAT_FP (nx_regs cx) (nx_ly cx) (nx_S cx) (nx_W cx) (nx_mem cx) (nx_md cx)
    EV_check_no_overread (fun ly' S' W' regs' mem' md' =>
      Permutation (ablocks B ly' S') (ablocks B (nx_ly cx) (nx_S cx)) /\
      fm_glob tfibsegs W' mem' (nx_live cx) (rt_peak (nx_ub cx) (nx_live cx) (nx_peak cx))
        (if (length (nx_ub cx) =? 0)%nat then nx_cnt cx else nx_cnt cx + 2) SIZE_MAXZ).

(* the walk's journal from the entry state *)
Definition cno_J (cx : cnx) ly' S' (W' : world tfibsegs) mem' md' (k : Z) : Prop :=
  ajournal tfibsegs B STK_check_no_overread (nx_sp0 cx) FM_PSTAT_FP (nx_ly cx) (nx_S cx) (nx_W cx) (nx_mem cx) (nx_md cx)
    [] ly' S' W' mem' md' k.

(* the saved registers in their slots above sp0 - 96 *)
Definition cno_frame (cx : cnx) (W : world tfibsegs) (m : word -> option byte) : Prop :=
  forall j o r, nth_error cno_saved_offs j = Some o -> nth_error cno_saved_regs j = Some r ->
    val_mem tfibsegs (rdW W m) (nx_sp0 cx - CNO_FRAME + o) 8 (bv_unsigned (getr (nx_regs cx) (Z_to_bv 5 r))).

(* what holds at every resume point after the prologue: the journal, the frame, sp/gp/tp, s8 = the shadow base, the
   relro view, s10/s11 as at the entry (the function never writes them and does not save them) *)
Definition cno_core (cx : cnx) ly' S' (W' : world tfibsegs) regs' mem' md' (k : Z) : Prop :=
  cno_J cx ly' S' W' mem' md' k /\ cno_frame cx W' mem' /\
  spZ regs' = nx_sp0 cx - CNO_FRAME /\ getr regs' 3 = getr (nx_regs cx) 3 /\ getr regs' 4 = getr (nx_regs cx) 4 /\
  getr regs' 24 = w64 FMW_SB /\
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem') /\
  getr regs' 26 = getr (nx_regs cx) 26 /\ getr regs' 27 = getr (nx_regs cx) 27.

(* the copy phase (P1 .. R4): the blocks are the entry's plus the copies made (in order), the journal counts one event per
   copy, the source bytes are as at the entry, the statics untouched, s2 = tp, s5 = up, s9 = un + 18 *)
Definition cno_cp (cx : cnx) ly' S' (W' : world tfibsegs) regs' mem' md' (nb : list (Z * Z)) : Prop :=
  cno_core cx ly' S' W' regs' mem' md' (Z.of_nat (length nb)) /\
  ablocks B ly' S' = ablocks B (nx_ly cx) (nx_S cx) ++ nb /\
  bytes_at tfibsegs W' mem' (nx_up cx) (nx_ub cx) /\ bytes_at tfibsegs W' mem' (nx_tp cx) (nx_tb cx) /\
  fm_glob tfibsegs W' mem' (nx_live cx) (nx_peak cx) (nx_cnt cx) SIZE_MAXZ /\
  getr regs' 18 = w64 (nx_tp cx) /\ getr regs' 21 = w64 (nx_up cx) /\ getr regs' 25 = w64 (nx_un cx + 18).
(* a copy at p of the bytes l: the bytes, then (once the NUL is stored) the NUL *)
Definition cno_cpy (W : world tfibsegs) (m : word -> option byte) (p : Z) (l : list Z) : Prop := garr8 tfibsegs (rdW W m) p l.

(* ---- the state at each resume point ---- *)
Definition cno_P1 (cx : cnx) ly' S' W' regs' mem' md' (u1 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md' [(u1, nx_un cx + 18)] /\ 4096 <= u1 /\
  getr regs' 10 = w64 u1 /\ getr regs' 9 = w64 (nx_tn cx) /\ getr regs' 20 = w64 (nx_un cx) /\
  getr regs' 23 = w64 (nx_un cx + 18).
Definition cno_Q1 (cx : cnx) ly' S' W' regs' mem' md' (u1 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md' [(u1, nx_un cx + 18)] /\ 4096 <= u1 /\
  getr regs' 8 = w64 u1 /\ getr regs' 9 = w64 (nx_tn cx) /\ getr regs' 20 = w64 (nx_un cx) /\
  getr regs' 23 = w64 (nx_un cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx).
Definition cno_R1 (cx : cnx) ly' S' W' regs' mem' md' (u1 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md' [(u1, nx_un cx + 18)] /\ 4096 <= u1 /\
  getr regs' 8 = w64 u1 /\ getr regs' 9 = w64 (nx_tn cx) /\ getr regs' 20 = w64 (nx_un cx) /\
  getr regs' 23 = w64 (nx_un cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]).
Definition cno_P2 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md' [(u1, nx_un cx + 18); (t1, nx_tn cx + 18)] /\ 4096 <= u1 /\ 4096 <= t1 /\
  getr regs' 10 = w64 t1 /\ getr regs' 8 = w64 u1 /\ getr regs' 9 = w64 (nx_tn cx) /\ getr regs' 20 = w64 (nx_un cx) /\
  getr regs' 22 = w64 (nx_tn cx + 18) /\ getr regs' 23 = w64 (nx_un cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]).
Definition cno_Q2 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md' [(u1, nx_un cx + 18); (t1, nx_tn cx + 18)] /\ 4096 <= u1 /\ 4096 <= t1 /\
  getr regs' 19 = w64 t1 /\ getr regs' 8 = w64 u1 /\ getr regs' 9 = w64 (nx_tn cx) /\ getr regs' 20 = w64 (nx_un cx) /\
  getr regs' 22 = w64 (nx_tn cx + 18) /\ getr regs' 23 = w64 (nx_un cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]) /\ cno_cpy W' mem' t1 (nx_tb cx).
Definition cno_R2 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md' [(u1, nx_un cx + 18); (t1, nx_tn cx + 18)] /\ 4096 <= u1 /\ 4096 <= t1 /\
  getr regs' 19 = w64 t1 /\ getr regs' 8 = w64 u1 /\ getr regs' 9 = w64 (nx_tn cx) /\ getr regs' 20 = w64 (nx_un cx) /\
  getr regs' 22 = w64 (nx_tn cx + 18) /\ getr regs' 23 = w64 (nx_un cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]) /\ cno_cpy W' mem' t1 (nx_tb cx ++ [0]).
Definition cno_P3 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 u2 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md' [(u1, nx_un cx + 18); (t1, nx_tn cx + 18); (u2, nx_un cx + 18)] /\
  4096 <= u1 /\ 4096 <= t1 /\ 4096 <= u2 /\
  getr regs' 10 = w64 u2 /\ getr regs' 19 = w64 t1 /\ getr regs' 8 = w64 u1 /\ getr regs' 9 = w64 (nx_tn cx) /\
  getr regs' 20 = w64 (nx_un cx) /\ getr regs' 22 = w64 (nx_tn cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]) /\ cno_cpy W' mem' t1 (nx_tb cx ++ [0]).
Definition cno_Q3 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 u2 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md' [(u1, nx_un cx + 18); (t1, nx_tn cx + 18); (u2, nx_un cx + 18)] /\
  4096 <= u1 /\ 4096 <= t1 /\ 4096 <= u2 /\
  getr regs' 23 = w64 u2 /\ getr regs' 19 = w64 t1 /\ getr regs' 8 = w64 u1 /\ getr regs' 9 = w64 (nx_tn cx) /\
  getr regs' 20 = w64 (nx_un cx) /\ getr regs' 22 = w64 (nx_tn cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]) /\ cno_cpy W' mem' t1 (nx_tb cx ++ [0]) /\ cno_cpy W' mem' u2 (nx_ub cx).
(* after memset (u2 + un, 0, 17): s4 = u2 + un + 17 (its byte not yet stored) *)
Definition cno_R3 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 u2 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md' [(u1, nx_un cx + 18); (t1, nx_tn cx + 18); (u2, nx_un cx + 18)] /\
  4096 <= u1 /\ 4096 <= t1 /\ 4096 <= u2 /\
  getr regs' 23 = w64 u2 /\ getr regs' 19 = w64 t1 /\ getr regs' 8 = w64 u1 /\ getr regs' 9 = w64 (nx_tn cx) /\
  getr regs' 20 = w64 (u2 + nx_un cx + 17) /\ getr regs' 22 = w64 (nx_tn cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]) /\ cno_cpy W' mem' t1 (nx_tb cx ++ [0]) /\ cno_cpy W' mem' u2 (nx_ub cx ++ [0]).
Definition cno_P4 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 u2 t2 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md'
    [(u1, nx_un cx + 18); (t1, nx_tn cx + 18); (u2, nx_un cx + 18); (t2, nx_tn cx + 18)] /\
  4096 <= u1 /\ 4096 <= t1 /\ 4096 <= u2 /\ 4096 <= t2 /\
  getr regs' 10 = w64 t2 /\ getr regs' 23 = w64 u2 /\ getr regs' 19 = w64 t1 /\ getr regs' 8 = w64 u1 /\
  getr regs' 9 = w64 (nx_tn cx) /\ getr regs' 22 = w64 (nx_tn cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]) /\ cno_cpy W' mem' t1 (nx_tb cx ++ [0]) /\ cno_cpy W' mem' u2 (nx_ub cx ++ [0]).
Definition cno_Q4 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 u2 t2 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md'
    [(u1, nx_un cx + 18); (t1, nx_tn cx + 18); (u2, nx_un cx + 18); (t2, nx_tn cx + 18)] /\
  4096 <= u1 /\ 4096 <= t1 /\ 4096 <= u2 /\ 4096 <= t2 /\
  getr regs' 20 = w64 t2 /\ getr regs' 23 = w64 u2 /\ getr regs' 19 = w64 t1 /\ getr regs' 8 = w64 u1 /\
  getr regs' 9 = w64 (nx_tn cx) /\ getr regs' 22 = w64 (nx_tn cx + 18) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]) /\ cno_cpy W' mem' t1 (nx_tb cx ++ [0]) /\ cno_cpy W' mem' u2 (nx_ub cx ++ [0]) /\
  cno_cpy W' mem' t2 (nx_tb cx).
(* after memset (t2 + tn, 0, 17): s1 = t2 + tn + 17 (its byte not yet stored) *)
Definition cno_R4 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 u2 t2 : Z) : Prop :=
  cno_cp cx ly' S' W' regs' mem' md'
    [(u1, nx_un cx + 18); (t1, nx_tn cx + 18); (u2, nx_un cx + 18); (t2, nx_tn cx + 18)] /\
  4096 <= u1 /\ 4096 <= t1 /\ 4096 <= u2 /\ 4096 <= t2 /\
  getr regs' 20 = w64 t2 /\ getr regs' 23 = w64 u2 /\ getr regs' 19 = w64 t1 /\ getr regs' 8 = w64 u1 /\
  getr regs' 9 = w64 (t2 + nx_tn cx + 17) /\
  cno_cpy W' mem' u1 (nx_ub cx ++ [0]) /\ cno_cpy W' mem' t1 (nx_tb cx ++ [0]) /\ cno_cpy W' mem' u2 (nx_ub cx ++ [0]) /\
  cno_cpy W' mem' t2 (nx_tb cx ++ [0]).

(* the reader phase (N1, N2): the four copies live (blocks a permutation of the entry's plus them), the statics after c
   reader calls (the first raises the peak to rt_peak) *)
Definition cno_glob (cx : cnx) (W' : world tfibsegs) mem' (c : Z) : Prop :=
  fm_glob tfibsegs W' mem' (nx_live cx)
    (if c =? 0 then nx_peak cx else rt_peak (nx_ub cx) (nx_live cx) (nx_peak cx))
    (if (length (nx_ub cx) =? 0)%nat then nx_cnt cx else nx_cnt cx + c) SIZE_MAXZ.
Definition cno_rd (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 u2 t2 k : Z) : Prop :=
  cno_core cx ly' S' W' regs' mem' md' k /\
  Permutation (ablocks B ly' S')
    (ablocks B (nx_ly cx) (nx_S cx) ++ [(u1, nx_un cx + 18); (t1, nx_tn cx + 18); (u2, nx_un cx + 18); (t2, nx_tn cx + 18)]) /\
  4096 <= u1 /\ 4096 <= t1 /\ 4096 <= u2 /\ 4096 <= t2 /\
  getr regs' 20 = w64 t2 /\ getr regs' 23 = w64 u2 /\ getr regs' 19 = w64 t1 /\ getr regs' 8 = w64 u1.
Definition cno_N1 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 u2 t2 : Z) : Prop :=
  cno_rd cx ly' S' W' regs' mem' md' u1 t1 u2 t2 (4 + EV_names) /\
  getr regs' 10 = w64 (ManifestModel.names (nx_tb cx) (nx_ub cx)) /\
  cno_cpy W' mem' u2 (nx_ub cx ++ [0]) /\ cno_cpy W' mem' t2 (nx_tb cx ++ [0]) /\
  cno_glob cx W' mem' 1.
Definition cno_N2 (cx : cnx) ly' S' W' regs' mem' md' (u1 t1 u2 t2 : Z) : Prop :=
  cno_rd cx ly' S' W' regs' mem' md' u1 t1 u2 t2 (4 + 2 * EV_names) /\
  getr regs' 10 = w64 (ManifestModel.names (nx_tb cx) (nx_ub cx)) /\
  getr regs' 9 = w64 (ManifestModel.names (nx_tb cx) (nx_ub cx)) /\
  cno_glob cx W' mem' 2.

(* the free phase (F1 .. F3): the copies not yet freed, the statics final *)
Definition cno_fr (cx : cnx) ly' S' W' regs' mem' md' (left : list (Z * Z)) (k : Z) : Prop :=
  cno_core cx ly' S' W' regs' mem' md' k /\
  Permutation (ablocks B ly' S') (ablocks B (nx_ly cx) (nx_S cx) ++ left) /\
  cno_glob cx W' mem' 2.
Definition cno_F1 (cx : cnx) ly' S' W' regs' mem' md' (t1 u2 t2 : Z) : Prop :=
  cno_fr cx ly' S' W' regs' mem' md' [(t1, nx_tn cx + 18); (u2, nx_un cx + 18); (t2, nx_tn cx + 18)] (5 + 2 * EV_names) /\
  getr regs' 20 = w64 t2 /\ getr regs' 23 = w64 u2 /\ getr regs' 19 = w64 t1 /\ s0Z regs' < alloc_ceiling.
Definition cno_F2 (cx : cnx) ly' S' W' regs' mem' md' (u2 t2 : Z) : Prop :=
  cno_fr cx ly' S' W' regs' mem' md' [(u2, nx_un cx + 18); (t2, nx_tn cx + 18)] (6 + 2 * EV_names) /\
  getr regs' 20 = w64 t2 /\ getr regs' 23 = w64 u2 /\ s0Z regs' < alloc_ceiling.
Definition cno_F3 (cx : cnx) ly' S' W' regs' mem' md' (t2 : Z) : Prop :=
  cno_fr cx ly' S' W' regs' mem' md' [(t2, nx_tn cx + 18)] (7 + 2 * EV_names) /\
  getr regs' 20 = w64 t2.

(* ---- the frame ---- *)
Lemma cno_saved_offs_range : forall j o, nth_error cno_saved_offs j = Some o -> 8 <= o <= 88.
Proof.
intros j o Ho. pose proof (nth_error_In _ _ Ho) as Hi.
assert (F : Forall (fun o => 8 <= o <= 88) cno_saved_offs) by (repeat constructor; lia).
exact (proj1 (Forall_forall _ _) F o Hi).
Qed.
Lemma cno_saved_regs_range : forall j r, nth_error cno_saved_regs j = Some r -> 0 <= r < 32.
Proof.
intros j r Hr. pose proof (nth_error_In _ _ Hr) as Hi.
assert (F : Forall (fun r => 0 <= r < 32) cno_saved_regs) by (repeat constructor; lia).
exact (proj1 (Forall_forall _ _) F r Hi).
Qed.
(* the frame is kept by any step that leaves [sp0 - 96, sp0) as it was *)
Lemma cno_frame_kept : forall cx (W W' : world tfibsegs) m m',
  (forall a, nx_sp0 cx - CNO_FRAME <= a < nx_sp0 cx -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  cno_frame cx W m -> cno_frame cx W' m'.
Proof.
intros cx W W' m m' HK HF j o r Ho Hr. eapply (val_mem_kept tfibsegs); [|exact (HF j o r Ho Hr)].
intros k Hk. pose proof (cno_saved_offs_range j o Ho). unfold CNO_FRAME. apply HK. unfold CNO_FRAME. cbn in Hk. lia.
Qed.
Lemma cno_frame_below : forall cx (W : world tfibsegs) m m',
  same_below m m' (2 ^ 64) -> 0 <= nx_sp0 cx - CNO_FRAME -> nx_sp0 cx <= 2 ^ 47 ->
  cno_frame cx W m -> cno_frame cx W m'.
Proof.
intros cx W m m' HS H0 H1. apply cno_frame_kept. intros a Ha.
apply (aview_below (w_H W) m m' (2 ^ 64) a HS). lia.
Qed.
(* the frame from the prologue's stack chunks (offsets relative to sp0; atom r = the entry register r) *)
Lemma cno_frame_of_chunks : forall cx (W : world tfibsegs) m lo hi wlo whi cs extra,
  region_ok tfibsegs (Ereg (nx_regs cx) extra) (rdW W m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  (forall j o r, nth_error cno_saved_offs j = Some o -> nth_error cno_saved_regs j = Some r ->
     In (YP09.mkChunk (o - CNO_FRAME) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  cno_frame cx W m.
Proof.
intros cx W m lo hi wlo whi cs extra HR Hcs j o r Ho Hr.
pose proof (cno_saved_regs_range j r Hr) as Rr.
assert (E2 : bv_unsigned (ew (Ereg (nx_regs cx) extra) 2) = nx_sp0 cx)
  by (rewrite (ew_Ereg_nat (nx_regs cx) extra 2 2%bv eq_refl); reflexivity).
pose proof (fmw_field _ _ 2 (nx_sp0 cx) cs lo hi wlo whi (o - CNO_FRAME) 8%N (SOff (Z.to_nat r) 0)
  (bv_unsigned (getr (nx_regs cx) (Z_to_bv 5 r))) HR E2 (Hcs j o r Ho Hr)) as V.
replace (nx_sp0 cx + (o - CNO_FRAME)) with (nx_sp0 cx - CNO_FRAME + o) in V by lia.
apply V.
- rewrite fmw_SOff0. rewrite (ew_Ereg_nat (nx_regs cx) extra (Z.to_nat r) (Z_to_bv 5 r)).
  + symmetry. apply Z_to_bv_bv_unsigned.
  + rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus. cbn [Z.of_N]. lia.
- apply u64_range.
- cbn; lia.
Qed.
End c.
