(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (258 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: XW2, asan.module_dtor's write footprint, is fuzz_reply.asan's: the two flag cells and the four shadow runs __asan_unregister_globals clears for this image's 27 asan_globals descriptors and their 1728-byte array (A/AE37.v x2_shw); cgif's were three globals' runs and its array's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/AE23.v, with its module paths, module names, addresses and numbers changed; 575 of its 666 lines of code are new or changed and 1676 lines of the source are left out. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m YA0e.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AE20 AE7f AE22.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AE3e AE3f AE3g AE6g AE2p AE3i AE3h AE3m AE23.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1u AD1w AD1o AD1k.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile LinkExitFile LinkDrvExitF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Ground work for exf_tail_tfa (LinkDrvExitF.v): the exit walk after __stdio_exit's open-file loop, from
   0x96890 with s0 = 0 through the rest of __stdio_exit (stdin, stdout, stderr) and _Exit.

   The symbolic state at 0x96890 is AE23.v's at A_exit with two changes, and nothing else:
   - the open-file head holds link's memory FILE f, so its cell is the atom 36, not the literal 0;
   - the walk starts INSIDE __stdio_exit's frame, so the stack region carries the two saved words that the
     epilogues read back: the exit code (the atom 37) at sp and the return address 0x90df4 at sp + 8, and the
     region reaches sp + 48 (exit's frame) instead of stopping at sp.
   The atoms are AE23's: 2 = sp, 32 = tid, 33 = the canary, 34 = stdout's write position, 35 = stderr's, and
   36 / 37 are new. The walk runs no intercepted call, so it needs no AR; that is why it can be stated over
   LinkDrvExitF.v's exf_mid, which carries none.

   What the three runs below settle (the measured shape of the tail, for whoever closes exf_tail_tfa):
   - with stdout pristine (k = 0) and with stdout's window open but empty (k = 1), the walk reaches the exit
     ecall 0x90b60 in ONE run: close_file writes nothing, so neither arm has a write to account for;
   - with stdout's window holding bytes (k >= 2) the walk stops at the writev ecall 0x96320 first, exactly as
     the released walk does (AE23.v xF_run5), so that arm takes AE23's two-run shape. *)

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* AE23's exit regions with the open-file head as the atom 36 *)
Definition exf_regions (fo : list YP09.chunk) : smem :=
  map (fun r => if Z.eqb (YP09.r_lo r) 0x652300
                then YP09.mkRegion None 0x652300 0x652310 0x652300 0x652300
                       [YP09.mkChunk 0x652300 (CVal 4 (SLit 0)); YP09.mkChunk 0x652308 (CVal 8 (SOff 36 0))]
                else r) (ex_regions fo).

(* __stdio_exit's frame: the exit code at sp, the return into exit at sp + 8 *)
Definition exf_stack : YP09.region :=
  YP09.mkRegion (Some 2%nat) (- VF_STK) 48 (- VF_STK) 48
    [YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SLit 0x90df4))].
(* The tail's regions. Besides the open-file head, the atexit table and exit's lock lose their chunks: the
   part of the exit before the loop writes them (__funcs_on_exit clears the slot it runs), so they are not
   constants of this walk, and nothing after the loop reads them. *)
Definition exf_tail_regions (fo : list YP09.chunk) : smem :=
  exf_stack :: map (fun r => if Z.eqb (YP09.r_lo r) 0x651c60
                             then YP09.mkRegion None 0x651c60 0x651d90 0x651c60 0x651d90 []
                             else if Z.eqb (YP09.r_lo r) 0x651e80
                             then YP09.mkRegion None 0x651e80 0x651e84 0x651e80 0x651e84 []
                             else r) (tl (exf_regions fo)).

Definition exf_rest : smem := Eval vm_compute in tl (tl (exf_tail_regions [])).

(* the region list splits into the frame, stdout's FILE and a part that does not depend on stdout *)
Lemma exf_tail_regions_eq : forall fo, exf_tail_regions fo =
  exf_stack :: YP09.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ) fo :: exf_rest.
Proof. intros fo. vm_compute. reflexivity. Qed.

(* a cell of exf_consts (AE23's ex_consts without the open-file head), by a check on the list *)
Definition exf_has (a : Z) (n : N) (v : Z) : bool :=
  existsb (fun c => ((fst (fst c) =? a) && N.eqb (snd (fst c)) n && (snd c =? v))%bool) exf_consts.

Lemma exf_cell : forall (m : word -> option byte) a n v,
cells_are exf_consts m -> exf_has a n v = true -> val_mem tfibsegs m a (N.to_nat n) v.
Proof.
intros m a n v HC Hb. unfold cells_are in HC. rewrite Forall_forall in HC.
unfold exf_has in Hb. apply existsb_exists in Hb. destruct Hb as ([[a' n'] v'] & Hin & Hc).
cbn [fst snd] in Hc. apply andb_prop in Hc as [Hc Hv]. apply andb_prop in Hc as [Ha Hn].
apply Z.eqb_eq in Ha. apply N.eqb_eq in Hn. apply Z.eqb_eq in Hv. subst a' n' v'.
exact (HC _ Hin).
Qed.

(* the three entry states: stdout pristine, stdout's window empty, stdout's window holding bytes *)
Definition exf_regP : smem := Eval vm_compute in exf_tail_regions (fo_chunks stdout_fields0).
Definition exf_regE : smem := Eval vm_compute in
  exf_tail_regions (YP09.mkChunk (F_STDOUT + 40) (CVal 8 (SLit STDOUT_BUFA)) :: fo_chunks stdout_fields1).
Definition exf_regF : smem := Eval vm_compute in
  exf_tail_regions (YP09.mkChunk (F_STDOUT + 40) (CVal 8 (SOff 34 0)) :: fo_chunks stdout_fields1).

Definition ssf_P : sstate := mkSS A_SX_NEXT sr_atoms exf_regP None ex_facts0.
Definition ssf_E : sstate := mkSS A_SX_NEXT sr_atoms exf_regE None ex_facts0.
Definition ssf_F : sstate := mkSS A_SX_NEXT sr_atoms exf_regF None ex_factsF.

Definition exf_stP : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL ssf_P).
Definition exf_stE : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL ssf_E).
Definition exf_stF : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL ssf_F).

(* stdout pristine: one run, to the exit ecall at 0x90b60 *)
Lemma exf_runP : sym_runN tfibsegs tfibmusl_tbl FUEL ssf_P = (exf_stP, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma exf_pcP : ss_pc exf_stP = 0x90b60.
Proof. vm_compute. reflexivity. Qed.

(* stdout's window open but empty: the same, nothing is written *)
Lemma exf_runE : sym_runN tfibsegs tfibmusl_tbl FUEL ssf_E = (exf_stE, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma exf_pcE : ss_pc exf_stE = 0x90b60.
Proof. vm_compute. reflexivity. Qed.

(* stdout's window holding bytes: the run stops at the writev ecall of __stdout_write first *)
Lemma exf_runF : sym_runN tfibsegs tfibmusl_tbl FUEL ssf_F = (exf_stF, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma exf_pcF : ss_pc exf_stF = 0x96320.
Proof. vm_compute. reflexivity. Qed.

Definition exf_env (regs : bvmap 5 word) (tid cval wp sew f code : Z) : YP0m.env :=
  Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew; Z_to_bv 64 f; Z_to_bv 64 code].

Ltac exf_pc HC a n v := pose proof (exf_cell _ a n v HC ltac:(vm_compute; reflexivity)).

Ltac exf_cells HC :=
  exf_pc HC 0xa2688 8%N 0xa1370; exf_pc HC 0xa2690 8%N 0xa1360;
  exf_pc HC 0xa1360 8%N 0x8864c; exf_pc HC 0xa1368 8%N 0x31328;
  exf_pc HC 0xa19a0 8%N 0x90c6c; exf_pc HC 0xa19a8 8%N 0;
  exf_pc HC 0xa6088 8%N 0xa5fa0; exf_pc HC 0xa6178 8%N 0xa6090; exf_pc HC 0xa6268 8%N 0xa6180;
  exf_pc HC 0x651c64 4%N 0; exf_pc HC 0x651c78 8%N 0;
  exf_pc HC 0x651c80 8%N 0x90d34; exf_pc HC 0x651c88 8%N 0x90d34;
  exf_pc HC 0x651d80 8%N 0x7178c; exf_pc HC 0x651d88 8%N 0x82154;
  exf_pc HC 0x5dca94 1%N 0; exf_pc HC 0x651ea3 1%N 0; exf_pc HC 0x652300 4%N 0;
  exf_pc HC 0xa6188 8%N 0; exf_pc HC 0xa6190 8%N 0; exf_pc HC 0xa61a8 8%N 0; exf_pc HC 0xa61b8 8%N 0;
  exf_pc HC 0xa620c 4%N 0xffffffff;
  exf_pc HC 0xa5fa8 8%N 0; exf_pc HC 0xa5fb0 8%N 0; exf_pc HC 0xa602c 4%N 0xffffffff.

Local Ltac WSEG := first
[ apply (wseg_writable _ 680080 232); [exact wz_stdout | lia | lia | lia | lia]
| apply (wseg_writable _ 679840 232); [exact wz_stderr | lia | lia | lia | lia]
| apply (wseg_writable _ 0x651c60 0x130); [exact wz_atexit | lia | lia | lia | lia]
| apply (wseg_writable _ 0x651e80 4); [exact wz_exitlock | lia | lia | lia | lia] ].
Local Ltac CELL :=
  (eapply (chunk_ok_val tfibsegs _ _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; assumption]).

Lemma exf_regP_eq : exf_regP =
  exf_stack :: YP09.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ)
                 (fo_chunks stdout_fields0) :: exf_rest.
Proof. vm_compute. reflexivity. Qed.

Lemma exf_regE_eq : exf_regE =
  exf_stack :: YP09.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ)
                 (YP09.mkChunk (F_STDOUT + 40) (CVal 8 (SLit STDOUT_BUFA)) :: fo_chunks stdout_fields1)
               :: exf_rest.
Proof. vm_compute. reflexivity. Qed.

(* the regions that do not depend on stdout: stderr, stdin, the canary, the exit tables, the open-file
   head (the atom 36) and the thread id *)
Lemma exf_rest_ok : forall (E : YP0m.env) (m : word -> option byte) (tid cval sew f : Z),
bv_unsigned (ew E 4) = 0x631c10 ->
ew E 32 = Z_to_bv 64 tid -> ew E 33 = Z_to_bv 64 cval -> ew E 35 = Z_to_bv 64 sew -> ew E 36 = Z_to_bv 64 f ->
cells_are exf_consts m ->
val_mem tfibsegs m (0x631c10 - 168) 4 tid ->
val_mem tfibsegs m 0xa2658 8 0x651c50 -> val_mem tfibsegs m 0x651c50 8 cval ->
val_mem tfibsegs m (0xa5fa0 + 40) 8 sew -> val_mem tfibsegs m (0xa5fa0 + 56) 8 sew ->
val_mem tfibsegs m 0x652308 8 f ->
0 < tid < 2 ^ 31 -> 0 <= cval < 2 ^ 64 -> 0 <= sew < 2 ^ 64 -> 0 <= f < 2 ^ 64 ->
Forall (region_ok tfibsegs E m) exf_rest.
Proof.
intros E m tid cval sew f E4 E32 E33 E35 E36 HC Mtid Mgot Mcan Msew1 Msew2 Mofl Rtid Rcan Rsew Rf.
exf_cells HC. unfold exf_rest.
repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
    repeat apply Forall_cons; try apply Forall_nil;
    first [ CELL
          | eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ sew);
            [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
             rewrite Z.add_0_l; assumption] ].
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    constructor; [|constructor].
    eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; exact Mgot].
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    constructor; [|constructor].
    eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
     rewrite Z.add_0_l; exact Mcan].
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    first [ CELL
          | eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ f);
            [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
             rewrite Z.add_0_l; exact Mofl] ].
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E4. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    constructor; [|constructor].
    eapply (chunk_ok_val tfibsegs E _ 0x631c10 (-168) 4 _ tid);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mtid].
Qed.
(* the state at 0x96890 with stdout pristine, from the facts exf_mid carries *)
Lemma exf_entryP : forall (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (usp code f tid cval sew wp : Z),
spZ regs = usp - 80 -> usp mod 16 = 0 -> sp_window_lo <= usp <= sp_window_hi ->
getr regs 4%bv = w64 TFIB_TPX ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 80) 8 code -> 0 <= code < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 72) 8 0x90df4 ->
cells_are exf_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_TPX - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x652308 8 f -> 0 <= f < 2 ^ 64 -> 0 <= wp < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
st_ok tfibsegs (exf_env regs tid cval wp sew f code) ssf_P
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_SX_NEXT) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem usp code f tid cval sew wp Hsp U16 [Ulo Uhi] H4 Hpres
  Mcode Rcode Mra HC Mtid Rtid Mgot Mcan Rcan Msew1 Msew2 Rsew Mofl Rf Rwp HFO.
unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
assert (HVF : VF_STK = 9104) by reflexivity.
unfold stdout_pristine, ofile_is, stdout_fields0 in HFO.
repeat match type of HFO with Forall _ (_ :: _) =>
  let h := fresh "HFf" in pose proof (Forall_inv HFO) as h; cbn beta iota in h; apply Forall_inv_tail in HFO end.
exf_cells HC.
unfold F_STDOUT, F_STDERR, FILE_SZ, A_GOT_canary, A_canary, TFIB_TPX in *.
rewrite restrict_mkst_fx. unfold ssf_P.
set (E := exf_env regs tid cval wp sew f code) in *.
assert (E2 : bv_unsigned (ew E 2) = usp - 80)
  by (subst E; unfold exf_env; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E4 : bv_unsigned (ew E 4) = 0x631c10)
  by (subst E; unfold exf_env; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 1)).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 code) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 5)).
apply (entry_st_ok_full tfibsegs);
change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew; Z_to_bv 64 f; Z_to_bv 64 code]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- rewrite exf_regP_eq.
  apply Forall_cons; [| apply Forall_cons].
  + unfold exf_stack, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply AE2y.apresent_writable; apply Hpres; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * eapply (chunk_ok_val tfibsegs E _ (usp - 80) 0 8 (SOff 37 0) code);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
       rewrite Z.add_0_r; exact Mcode].
    * eapply (chunk_ok_val tfibsegs E _ (usp - 80) 8 8 (SLit 0x90df4) 0x90df4);
      [reflexivity | zside | zside | replace (usp - 80 + 8) with (usp - 72) by lia; exact Mra].
  + unfold F_STDOUT, FILE_SZ, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
    unfold fo_chunks, stdout_fields0, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + exact (exf_rest_ok E _ tid cval sew f E4 E32 E33 E35 E36 HC Mtid Mgot Mcan Msew1 Msew2 Mofl Rtid Rcan Rsew Rf).
- apply pairwise_disjoint_of_extents. unfold exf_regP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E4.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [ex_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. repeat split; try lia.
Qed.

(* the whole tail with stdout pristine: 0x96890 to the exit ecall *)
Lemma exf_tail_P : forall (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (usp code f tid cval sew wp : Z),
spZ regs = usp - 80 -> usp mod 16 = 0 -> sp_window_lo <= usp <= sp_window_hi ->
getr regs 4%bv = w64 TFIB_TPX ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 80) 8 code -> (code = 0 \/ code = 2) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 72) 8 0x90df4 ->
cells_are exf_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_TPX - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x652308 8 f -> 0 <= f < 2 ^ 64 -> 0 <= wp < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
AI tfibsegs (w_H W) (w_A W) md ->
srealizes tfibsegs (cfg_at tfibsegs A_SX_NEXT regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
intros W regs mem md usp code f tid cval sew wp Hsp U16 Uw H4 Hpres Mcode Hc02 Mra HC
  Mtid Rtid Mgot Mcan Rcan Msew1 Msew2 Rsew Mofl Rf Rwp HFO HAI.
pose proof (exf_entryP W regs mem usp code f tid cval sew wp Hsp U16 Uw H4 Hpres Mcode
  ltac:(lia) Mra HC Mtid Rtid Mgot Mcan Rcan Msew1 Msew2 Rsew Mofl Rf Rwp HFO) as HS.
set (E := exf_env regs tid cval wp sew f code) in *.
assert (E37 : ew E 37 = Z_to_bv 64 code) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 5)).
unfold cfg_at. change (w64 A_SX_NEXT) with (Z_to_bv 64 A_SX_NEXT).
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E ssf_P exf_stP _ _ md HS exf_runP) HAI).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
rewrite <- (m_fs_wvb (m_vm_lazy md) mat1 md).
apply (srz_sym_exit W E exf_stP ms1 _ (Z_to_bv 64 code) HAI1 HS1 eq_refl eq_refl);
[| rewrite unsigned_lit_small by lia; lia].
match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, E37, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* the state at 0x96890 with stdout's window open but empty *)
Lemma exf_entryE : forall (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (usp code f tid cval sew wp : Z),
spZ regs = usp - 80 -> usp mod 16 = 0 -> sp_window_lo <= usp <= sp_window_hi ->
getr regs 4%bv = w64 TFIB_TPX ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 80) 8 code -> 0 <= code < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 72) 8 0x90df4 ->
cells_are exf_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_TPX - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x652308 8 f -> 0 <= f < 2 ^ 64 -> 0 <= wp < 2 ^ 64 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem) ->
st_ok tfibsegs (exf_env regs tid cval wp sew f code) ssf_E
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_SX_NEXT) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem usp code f tid cval sew wp Hsp U16 [Ulo Uhi] H4 Hpres
  Mcode Rcode Mra HC Mtid Rtid Mgot Mcan Rcan Msew1 Msew2 Rsew Mofl Rf Rwp HFO.
unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
assert (HVF : VF_STK = 9104) by reflexivity.
unfold stdout_mid in HFO. destruct HFO as [HFO Mwp40].
unfold ofile_is, stdout_fields1 in HFO.
repeat match type of HFO with Forall _ (_ :: _) =>
  let h := fresh "HFf" in pose proof (Forall_inv HFO) as h; cbn beta iota in h; apply Forall_inv_tail in HFO end.
exf_cells HC.
unfold F_STDOUT, F_STDERR, FILE_SZ, A_GOT_canary, A_canary, TFIB_TPX in *.
rewrite restrict_mkst_fx. unfold ssf_E.
set (E := exf_env regs tid cval wp sew f code) in *.
assert (E2 : bv_unsigned (ew E 2) = usp - 80)
  by (subst E; unfold exf_env; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E4 : bv_unsigned (ew E 4) = 0x631c10)
  by (subst E; unfold exf_env; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 1)).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 code) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 5)).
apply (entry_st_ok_full tfibsegs);
change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew; Z_to_bv 64 f; Z_to_bv 64 code]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- rewrite exf_regE_eq.
  apply Forall_cons; [| apply Forall_cons].
  + unfold exf_stack, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply AE2y.apresent_writable; apply Hpres; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * eapply (chunk_ok_val tfibsegs E _ (usp - 80) 0 8 (SOff 37 0) code);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
       rewrite Z.add_0_r; exact Mcode].
    * eapply (chunk_ok_val tfibsegs E _ (usp - 80) 8 8 (SLit 0x90df4) 0x90df4);
      [reflexivity | zside | zside | replace (usp - 80 + 8) with (usp - 72) by lia; exact Mra].
  + unfold F_STDOUT, FILE_SZ, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
    unfold fo_chunks, stdout_fields1, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + exact (exf_rest_ok E _ tid cval sew f E4 E32 E33 E35 E36 HC Mtid Mgot Mcan Msew1 Msew2 Mofl Rtid Rcan Rsew Rf).
- apply pairwise_disjoint_of_extents. unfold exf_regE, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E4.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [ex_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. repeat split; try lia.
Qed.

(* the whole tail with stdout's window open but empty: 0x96890 to the exit ecall *)
Lemma exf_tail_E : forall (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (usp code f tid cval sew wp : Z),
spZ regs = usp - 80 -> usp mod 16 = 0 -> sp_window_lo <= usp <= sp_window_hi ->
getr regs 4%bv = w64 TFIB_TPX ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 80) 8 code -> (code = 0 \/ code = 2) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 72) 8 0x90df4 ->
cells_are exf_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_TPX - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x652308 8 f -> 0 <= f < 2 ^ 64 -> 0 <= wp < 2 ^ 64 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem) ->
AI tfibsegs (w_H W) (w_A W) md ->
srealizes tfibsegs (cfg_at tfibsegs A_SX_NEXT regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
intros W regs mem md usp code f tid cval sew wp Hsp U16 Uw H4 Hpres Mcode Hc02 Mra HC
  Mtid Rtid Mgot Mcan Rcan Msew1 Msew2 Rsew Mofl Rf Rwp HFO HAI.
pose proof (exf_entryE W regs mem usp code f tid cval sew wp Hsp U16 Uw H4 Hpres Mcode
  ltac:(lia) Mra HC Mtid Rtid Mgot Mcan Rcan Msew1 Msew2 Rsew Mofl Rf Rwp HFO) as HS.
set (E := exf_env regs tid cval wp sew f code) in *.
assert (E37 : ew E 37 = Z_to_bv 64 code) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 5)).
unfold cfg_at. change (w64 A_SX_NEXT) with (Z_to_bv 64 A_SX_NEXT).
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E ssf_E exf_stE _ _ md HS exf_runE) HAI).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
rewrite <- (m_fs_wvb (m_vm_lazy md) mat1 md).
apply (srz_sym_exit W E exf_stE ms1 _ (Z_to_bv 64 code) HAI1 HS1 eq_refl eq_refl);
[| rewrite unsigned_lit_small by lia; lia].
match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, E37, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* stdout's window holding bytes: after the writev ecall, __stdout_write's iovec frame is at the atom 2
   minus 112 (AE23.v's -144 at A_exit, where the atom 2 is 32 higher than it is here), and the junk
   registers take the atoms from 38 on, the first free atom of this walk. The second run reaches the same
   exit ecall 0x90b60. *)
Definition exf_afF : sstate := Eval vm_compute in AE3g.wl_after exf_stF 0 (-112) 38.
Definition exf_st2F : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL exf_afF).

Lemma exf_runF2 : sym_runN tfibsegs tfibmusl_tbl FUEL exf_afF = (exf_st2F, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma exf_pcF2 : ss_pc exf_st2F = 0x90b60.
Proof. vm_compute. reflexivity. Qed.

Lemma exf_regF_eq : exf_regF =
  exf_stack :: YP09.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ)
                 (YP09.mkChunk (F_STDOUT + 40) (CVal 8 (SOff 34 0)) :: fo_chunks stdout_fields1)
               :: exf_rest.
Proof. vm_compute. reflexivity. Qed.

(* the state at 0x96890 with stdout's window holding bytes, its write position the atom 34 *)
Lemma exf_entryF : forall (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (usp code f tid cval sew wp : Z),
spZ regs = usp - 80 -> usp mod 16 = 0 -> sp_window_lo <= usp <= sp_window_hi ->
getr regs 4%bv = w64 TFIB_TPX ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 80) 8 code -> 0 <= code < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 72) 8 0x90df4 ->
cells_are exf_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_TPX - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x652308 8 f -> 0 <= f < 2 ^ 64 ->
stdout_mid wp (mrestrict (w_H W) mem) -> STDOUT_BUFA + 1 <= wp <= STDOUT_BUFA + STDOUT_BSZ ->
st_ok tfibsegs (exf_env regs tid cval wp sew f code) ssf_F
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_SX_NEXT) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem usp code f tid cval sew wp Hsp U16 [Ulo Uhi] H4 Hpres
  Mcode Rcode Mra HC Mtid Rtid Mgot Mcan Rcan Msew1 Msew2 Rsew Mofl Rf [HFO Mwp40] Rwp.
unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
assert (HVF : VF_STK = 9104) by reflexivity.
unfold ofile_is, stdout_fields1 in HFO.
repeat match type of HFO with Forall _ (_ :: _) =>
  let h := fresh "HFf" in pose proof (Forall_inv HFO) as h; cbn beta iota in h; apply Forall_inv_tail in HFO end.
exf_cells HC.
unfold F_STDOUT, F_STDERR, FILE_SZ, A_GOT_canary, A_canary, TFIB_TPX in *.
rewrite restrict_mkst_fx. unfold ssf_F.
set (E := exf_env regs tid cval wp sew f code) in *.
assert (E2 : bv_unsigned (ew E 2) = usp - 80)
  by (subst E; unfold exf_env; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E4 : bv_unsigned (ew E 4) = 0x631c10)
  by (subst E; unfold exf_env; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 wp) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 code) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 5)).
apply (entry_st_ok_full tfibsegs);
change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew; Z_to_bv 64 f; Z_to_bv 64 code]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- rewrite exf_regF_eq.
  apply Forall_cons; [| apply Forall_cons].
  + unfold exf_stack, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply AE2y.apresent_writable; apply Hpres; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * eapply (chunk_ok_val tfibsegs E _ (usp - 80) 0 8 (SOff 37 0) code);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
       rewrite Z.add_0_r; exact Mcode].
    * eapply (chunk_ok_val tfibsegs E _ (usp - 80) 8 8 (SLit 0x90df4) 0x90df4);
      [reflexivity | zside | zside | replace (usp - 80 + 8) with (usp - 72) by lia; exact Mra].
  + unfold F_STDOUT, FILE_SZ, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
    unfold fo_chunks, stdout_fields1, STDOUT_BUFA, STDOUT_BSZ in *. cbn [map Z.add].
    repeat apply Forall_cons; try apply Forall_nil;
    first [ CELL
          | eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ wp);
            [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
             rewrite Z.add_0_l; exact Mwp40] ].
  + exact (exf_rest_ok E _ tid cval sew f E4 E32 E33 E35 E36 HC Mtid Mgot Mcan Msew1 Msew2 Mofl Rtid Rcan Rsew Rf).
- apply pairwise_disjoint_of_extents. unfold exf_regF, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E4.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [ex_factsF f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E34, (unsigned_lit_small wp) by (unfold STDOUT_BUFA, STDOUT_BSZ in *; lia).
  change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  unfold STDOUT_BUFA, STDOUT_BSZ in *. repeat split; try lia.
Qed.

Local Ltac GEO :=
  unfold STDOUT_BUFA, STDOUT_BSZ, F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary,
         TFIB_TPX, VF_STK, ESTACK in *; lia.

(* no write window of the entry state reaches stdout's buffer, so its bytes survive the first run *)
Lemma exf_buf_kept : forall (E : YP0m.env) (sp0 a : Z),
bv_unsigned (ew E 2) = sp0 -> 2 ^ 40 <= sp0 ->
in_wrange E (ss_mem ssf_F) a -> ~ (STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ).
Proof.
intros E sp0 a E2 Hsp Hin Hb.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold ssf_F, exf_regF in Ht. cbn in Ht. unfold STDOUT_BUFA, STDOUT_BSZ in Hb.
repeat (destruct Ht as [Hq|Ht];
  [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?E2 in Hr; lia|]).
destruct Ht.
Qed.

(* the whole tail with stdout's window holding bytes: 0x96890, the writev of those bytes, the exit ecall *)
Lemma exf_tail_F : forall (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (usp code f tid cval sew wp : Z) (pend : list byte) ch,
spZ regs = usp - 80 -> usp mod 16 = 0 -> sp_window_lo <= usp <= sp_window_hi ->
getr regs 4%bv = w64 TFIB_TPX ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 80) 8 code -> (code = 0 \/ code = 2) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 72) 8 0x90df4 ->
cells_are exf_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_TPX - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x652308 8 f -> 0 <= f < 2 ^ 64 ->
stdout_mid wp (mrestrict (w_H W) mem) ->
wp = STDOUT_BUFA + Z.of_nat (length pend) -> (0 < length pend)%nat -> wp <= STDOUT_BUFA + STDOUT_BSZ ->
(forall i, (i < length pend)%nat ->
   aview tfibsegs (w_H W) mem (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend (Z_to_bv 8 0)))) ->
fdchan (Z_to_bv 64 1) ch md ->
AI tfibsegs (w_H W) (w_A W) md ->
srealizes tfibsegs (cfg_at tfibsegs A_SX_NEXT regs mem md)
  (t_emit (map (WriteEv ch) pend) (t_exit (Z_to_bv 64 code) (m_fs md))).
Proof.
intros W regs mem md usp code f tid cval sew wp pend ch Hsp U16 Uw H4 Hpres Mcode Hc02 Mra HC
  Mtid Rtid Mgot Mcan Rcan Msew1 Msew2 Rsew Mofl Rf HFO Hwp Hpendlen Hwphi HPEND Hch HAI.
pose proof Uw as [Ulo Uhi]. unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
pose proof (exf_entryF W regs mem usp code f tid cval sew wp Hsp U16 Uw H4 Hpres Mcode
  ltac:(lia) Mra HC Mtid Rtid Mgot Mcan Rcan Msew1 Msew2 Rsew Mofl Rf HFO ltac:(GEO)) as HS.
set (E := exf_env regs tid cval wp sew f code) in *.
assert (E2 : bv_unsigned (ew E 2) = usp - 80)
  by (subst E; unfold exf_env; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E34 : ew E 34 = Z_to_bv 64 wp) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 2)).
assert (E37 : ew E 37 = Z_to_bv 64 code) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 5)).
assert (E34u : bv_unsigned (ew E 34) = wp) by (rewrite E34; apply unsigned_lit_small; GEO).
unfold cfg_at. change (w64 A_SX_NEXT) with (Z_to_bv 64 A_SX_NEXT).
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E ssf_F exf_stF _ _ md HS exf_runF) HAI).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
rewrite ?wvb_wvb in HAI1 |- *.
assert (B0 : (0%bv : byte) = Z_to_bv 8 0) by (apply bv_eq; reflexivity).
assert (PEND1 : forall i, (i < length pend)%nat ->
  aview tfibsegs (w_H W) (ms_mem ms1) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite B0. rewrite <- (HPEND i Hi). apply aview_eq_of. apply HFr1.
  rewrite unsigned_lit_small by GEO. intros Hin.
  exact (exf_buf_kept E (usp - 80) _ E2 ltac:(GEO) Hin ltac:(GEO)). }
clear HF1 HFr1.
pose proof HS1 as HSc1. destruct HSc1 as (_ & _ & _ & _ & _ & _ & Hregs1 & Hmem1 & HG1).
cbn [restrict ms_mem] in Hmem1.
pose proof (lit_buf_sound tfibsegs E (mrestrict (w_H W) (ms_mem ms1)) (ss_mem exf_stF)
  (SLit (F_STDOUT + 120)) 4 [1; 0; 0; 0] Hmem1 ltac:(vm_compute; reflexivity)) as Hfdrd.
cbn [sv_denot] in Hfdrd.
replace (map (WriteEv ch) pend) with (map (WriteEv ch) (pend ++ [])) by (rewrite app_nil_r; reflexivity).
eapply (srz_sym_stdio_writev2 W E exf_stF ms1 _ (Z_to_bv 64 1) ch 0 2 (-112) F_STDOUT _
  (SLit STDOUT_BUFA) (SOff 34 (- STDOUT_BUFA)) (SLit 0) (SLit 0)
  pend [] (map (Z_to_bv 8) [1; 0; 0; 0]) 38 _ HAI1 HS1 eq_refl eq_refl eq_refl).
- reflexivity.
- eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same].
- reflexivity.
- vm_compute. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
  rewrite iovcnt_val, U_off, U_SLit by (rewrite E34u; unfold M64; GEO). rewrite E34u.
  rewrite (zcanon_id _) by (unfold M64; GEO). rewrite (proj2 (Z.eqb_neq _ _)) by GEO. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
  rewrite iovcnt_val', U_off, U_SLit by (rewrite E34u; unfold M64; GEO). rewrite E34u.
  rewrite (zcanon_id _) by (unfold M64; GEO). rewrite (proj2 (Z.eqb_neq _ _)) by GEO. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
  rewrite !U_off, U_SLit by (rewrite ?E34u; unfold M64; GEO). change (zcanon 0) with 0. GEO.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
  rewrite U_SLit. reflexivity.
- reflexivity.
- reflexivity.
- cbn. lia. - cbn. lia. - cbn. lia. - cbn. lia.
- vm_compute. reflexivity.
- rewrite word_to_nat_U, U_off by (rewrite E34u; unfold M64; GEO). cbn [sv_denot]. rewrite E34u.
  replace (Z.to_nat (wp + - STDOUT_BUFA)) with (length pend) by GEO.
  exact (rdn_of_aview (w_H W) (ms_mem ms1) STDOUT_BUFA pend PEND1).
- reflexivity.
- rewrite U_off, U_SLit by (rewrite E34u; unfold M64; GEO). rewrite E34u.
  change (zcanon 0) with 0. GEO.
- rewrite U_off, U_SLit by (rewrite E34u; unfold M64; GEO). rewrite E34u.
  rewrite (zcanon_id _) by (unfold M64; GEO). GEO.
- rewrite U_off, U_SLit, E2 by (rewrite E34u; unfold M64; GEO). rewrite E34u.
  rewrite (zcanon_id _) by (unfold M64; GEO). GEO.
- rewrite !U_SLit. change (zcanon 0) with 0. lia.
- rewrite !U_SLit, E2. change (zcanon 0) with 0. lia.
- exact Hfdrd.
- vm_compute. reflexivity.
- GEO.
- GEO.
- rewrite E2. GEO.
- rewrite E2. lia.
- rewrite E2. lia.
- vm_compute. reflexivity.
- intros ms1' ws1 mat1' HS1' HF1' HFr1' HAI1'. rewrite ?wvb_wvb in HAI1' |- *.
  change (AE3g.wl_after exf_stF 0 (-112) 38) with exf_afF in HS1'.
  remember (havoc E 38 ws1) as E1 eqn:HE1.
  assert (OLD1 : forall j, (j < 38)%nat -> ew E1 j = ew E j)
    by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
  assert (E37' : ew E1 37 = Z_to_bv 64 code) by (rewrite OLD1 by (cbv; lia); exact E37).
  clear HE1 HS1 Hfdrd Hregs1 Hmem1 HG1 HF1' HFr1' PEND1.
  eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E1 exf_afF exf_st2F _ _ _ HS1' exf_runF2) HAI1').
  intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2).
  rewrite ?wvb_wvb in HAI2 |- *.
  rewrite <- (m_fs_wvb (m_vm_lazy md) mat2 md).
  apply (srz_sym_exit W E1 exf_st2F ms2 _ (Z_to_bv 64 code) HAI2 HS2 eq_refl eq_refl);
  [| rewrite unsigned_lit_small by lia; lia].
  match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
  cbn [sv_denot]. rewrite Z.add_0_r, E37', Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* the open-file head, from the GI conjunct of exf_mid *)
Lemma exf_file_head : forall (W : world tfibsegs) (mem : word -> option byte) f,
amf_gi tfibsegs link_amf [(f, AMF_BLOCK)] (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x652308 8 f.
Proof.
intros W mem f Hgi.
destruct Hgi as [(_ & Hnil) | (f' & Hheads & Hl & _)]; [discriminate Hnil|].
injection Hl as Hff. subst f'.
exact (proj2 (proj2 Hheads)).
Qed.

Section t.
Variable B : asyms.

(* exf_tail_tfa (LinkDrvExitF.v) at the driver's stdout state AD1k.xst: the three arms assembled *)
Theorem exf_tail_link : exf_tail_tfa B AD1k.xst.
Proof.
intros W regs mem md usp code f k fs tid cval sew HAI MID R8.
pose proof MID as (Msp & M16 & Musp & Mgp & Mtp & Mtpx & Mpres & Mcode & Mc02 & Mra & Mra2 & Mcells &
  Mtid & Mtidr & Mgot & Mcan & Mcanr & Msew1 & Msew2 & Msewr & Mso & Mfds & Mfs & Mgi & Mf4 & Mf16 & Mfh & _).
assert (H4 : getr regs 4%bv = w64 TFIB_TPX) by (rewrite Mtp, Mtpx; reflexivity).
assert (Mtid' : val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_TPX - 168) 4 tid)
  by (rewrite <- Mtpx; exact Mtid).
assert (Mofl : val_mem tfibsegs (mrestrict (w_H W) mem) 0x652308 8 f) by (exact (exf_file_head W mem f Mgi)).
assert (Rf : 0 <= f < 2 ^ 64) by (unfold AMF_BLOCK in Mfh; lia).
rewrite <- Mfs.
destruct Mso as [[Hk0 HSI] | [Hk1 HX]].
- (* k = 0: stdout holds its image bytes *)
  subst k. unfold wr, ex. cbn [Nat.sub repeat concat map].
  apply (srz_conseq tfibsegs _ (t_exit (Z_to_bv 64 code) (m_fs md)));
  [| apply t_eq_sym; apply t_emit_nil_eq; apply t_emit_has_nil].
  exact (exf_tail_P W regs mem md usp code f tid cval sew STDOUT_BUFA Msp M16 Musp H4 Mpres Mcode Mc02 Mra
    Mcells Mtid' Mtidr Mgot Mcan Mcanr Msew1 Msew2 Msewr Mofl Rf ltac:(unfold STDOUT_BUFA; lia)
    (AD1o.stdout_pristine_img _ _ HSI) HAI).
- pose proof HX as (_ & Hcap & Hmid & HPEND).
  destruct (Nat.eq_dec k 1) as [-> | Hk2].
  + (* k = 1: stdout's window is open and empty *)
    unfold wr, ex. cbn [Nat.sub repeat concat map].
    apply (srz_conseq tfibsegs _ (t_exit (Z_to_bv 64 code) (m_fs md)));
    [| apply t_eq_sym; apply t_emit_nil_eq; apply t_emit_has_nil].
    replace (STDOUT_BUFA + 2 * (Z.of_nat 1 - 1)) with STDOUT_BUFA in Hmid by lia.
    exact (exf_tail_E W regs mem md usp code f tid cval sew STDOUT_BUFA Msp M16 Musp H4 Mpres Mcode Mc02 Mra
      Mcells Mtid' Mtidr Mgot Mcan Mcanr Msew1 Msew2 Msewr Mofl Rf ltac:(unfold STDOUT_BUFA; lia) Hmid HAI).
  + (* k >= 2: stdout's window holds the lines written so far *)
    assert (Hlen : length (concat (repeat line0 (k - 1))) = (2 * (k - 1))%nat) by apply AD1k.length_pend.
    assert (Hwp : STDOUT_BUFA + 2 * (Z.of_nat k - 1) =
                  STDOUT_BUFA + Z.of_nat (length (concat (repeat line0 (k - 1))))) by (rewrite Hlen; lia).
    assert (Hch : fdchan (Z_to_bv 64 1) ch_stdout md)
      by (split; [rewrite Mfds; vm_compute; reflexivity | reflexivity]).
    unfold wr, ex.
    exact (exf_tail_F W regs mem md usp code f tid cval sew (STDOUT_BUFA + 2 * (Z.of_nat k - 1))
      (concat (repeat line0 (k - 1))) ch_stdout Msp M16 Musp H4 Mpres Mcode Mc02 Mra
      Mcells Mtid' Mtidr Mgot Mcan Mcanr Msew1 Msew2 Msewr Mofl Rf Hmid Hwp ltac:(rewrite Hlen; lia)
      ltac:(unfold STDOUT_BSZ in *; lia) HPEND Hch HAI).
Qed.

End t.

End p.
