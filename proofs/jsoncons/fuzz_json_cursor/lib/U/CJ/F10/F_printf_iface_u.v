(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import SFModel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import ITree.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Nodes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Decode.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Monad.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import FmtFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Driver.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_memset_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_memcpy_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fwritex_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_pad_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_lib_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_pop_arg_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import Exit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import Printf_model.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import FmtFpNF.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation rsegs := F_memset_u.rsegs.
Notation mem := (word -> option byte).

Definition OUT_DEPTH : Z := 1024.
Definition PC_DEPTH : Z := 5184.
Definition VF_DEPTH : Z := 5552.
Definition GLOBALS_TOP : Z := 0xf8000.
Definition STATIC_SPLIT : Z := 0x20000.

Section Sink.
  Context {St : Type}.
  Variables (Fp B BS : Z).
  Variable SINK : mem -> St -> Prop.
  Variable TOPOK : Z -> Prop.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

  Definition SR : list (Z * Z) := [(Fp, Fp + 232); (B, B + BS)].

  Definition sink_frame_stmt : Prop :=
    forall (W : list (Z * Z)) (m m' : mem) (st : St),
      SINK m st -> munch W m m' -> wmono rsegs m m' ->
      Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv) W ->
      Forall (fun iv => snd iv <= B \/ B + BS <= fst iv) W ->
      SINK m' st.

  Definition sink_flags_stmt : Prop :=
    forall m st, SINK m st -> exists fl : byte, rw_cells rsegs m Fp [CB 1 [fl]] /\ Z.land (bv_unsigned fl) 32 = 0.

  Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.

  Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (S : Z) (bs : list Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ bytes_at rsegs m' S (zb bs).

  Definition out_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (bs : list Z) (lo : Z) (canary : word),
      SINK m st ->
      bytes_at rsegs m (bv_unsigned a0) (zb bs) ->
      Forall (fun c => 0 <= c < 256) bs -> zlength bs < 2^31 ->
      a1 = Z_to_bv 64 (zlength bs) ->
      a2 = Z_to_bv 64 Fp ->
      stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary ->
      mem_inv rsegs m ->
      (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
      (bv_unsigned a0 + zlength bs <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength bs <= Fp \/ Fp + 232 <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength bs <= B \/ B + BS <= bv_unsigned a0) ->
      implM rsegs (OUT bs) st
            (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) bs lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xacadc) fc None m (seg_rom rsegs)).

  Definition fpcall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ SINK m' st'
      /\ ssp_cells m' canary.

  Definition fpcall_stmt (c : Z * Z * Z * Z * Z) : Prop :=
    let '(y, w, p, fl, t) := c in
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      SINK m st ->
      y = bv_unsigned a1 + 2^64 * bv_unsigned a2 ->
      a0 = Z_to_bv 64 Fp -> a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t ->
      bv_unsigned a7 <> 5 ->
      (-2^31 <= w <= 1) -> (-2^31 <= p < 2^20) -> (0 <= fl < 2^32) -> (0 <= t < 256) -> Z.lor t 32 <> 97 ->
      stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FMT_FP_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary ->
      mem_inv rsegs m -> frm0 fc ->
      (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
      implM rsegs (OUTFP y w p fl t) st
            (fpcall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xae170) fc None m (seg_rom rsegs)).

  Definition arg_ok (m : mem) (lo sp ap : Z) (slot : word) (a : parg) : Prop :=
    match a with
    | PA_s s => exists slack : list byte,
        bytes_at rsegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
        /\ Forall (fun c => 0 < c < 256) s
        /\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
        /\ 0 < bv_unsigned slot
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned slot)
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= bv_unsigned slot)
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= B \/ B + BS <= bv_unsigned slot)
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= ap \/ ap + 8 <= bv_unsigned slot)
    | PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
    | PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
    | PA_g d => bv_unsigned slot = d
    end.
  Fixpoint args_ok (m : mem) (lo sp ap : Z) (slots : list word) (args : list parg) : Prop :=
    match args with
    | [] => True
    | a :: args' => match slots with
                    | [] => False
                    | w :: slots' => arg_ok m lo sp ap w a /\ args_ok m lo sp ap slots' args'
                    end
    end.

  Definition printf_core_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (AP lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch ((lo, bv_unsigned sp) :: (AP, AP + 8) :: SR) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ rw_cells rsegs m' AP [C8 apv]
      /\ (0 <= r <= INT_MAX).

  Definition printf_core_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word)
           (fmt : list Z) (VA i : Z) (slots : list word) (args : list parg),
      SINK m st ->
      bytes_at rsegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
      a0 = Z_to_bv 64 Fp ->
      rw_cells rsegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
      va_area m VA slots -> 0 <= i -> args_ok m lo (bv_unsigned sp) (bv_unsigned a2) (skipn (Z.to_nat i) slots) args ->
      Forall fpcall_stmt (fp_calls (length fmt) fmt args) ->
      stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->

      (bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> (0 <= BS) ->
      ((801360 <= Fp /\ Fp + 232 <= 1010288) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
      ((1010296 <= B /\ B + BS <= lo) \/ (bv_unsigned a2 + 8 <= B /\ B + BS <= VA)) ->
      (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      implM rsegs (printf_model OUT OUTFP fmt args) st
            (printf_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xad138) fc None m (seg_rom rsegs)).
End Sink.

Definition printf_core1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary.

Definition printf_core1_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (fmt : list Z),
    bytes_at rsegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
    pass1_ok fmt = true ->
    a0 = Z_to_bv 64 0 ->
    stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) ->
    ssp_cells m canary -> mem_inv rsegs m ->
    (bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) ->
    (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 2^64) ->
    evt rsegs (printf_core1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xad138) fc None m (seg_rom rsegs)).

Section SnSink.

  Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
  Definition SN_CAP : Z := 80.

  Definition SINK_sn (m : mem) (o : list Z) : Prop :=
    exists junk : list byte,
      wfile m Fp fl0 j1 j2 lbfw B (zb o) junk
      /\ rw_cells rsegs m (Fp + 148) frest /\ Z.of_nat (cells_size frest) = 84
      /\ zlength o + zlength junk = SN_CAP
      /\ (B + SN_CAP <= Fp \/ Fp + 232 <= B)
      /\ TOP <= Fp /\ TOP <= B.
  Definition TOPOK_sn (sp : Z) : Prop := sp <= TOP.

  Definition OUT_sn (bs : list Z) : M (list Z) unit :=
    o <- mget ;; if zlength o + zlength bs <=? SN_CAP then mput (o ++ bs) else munr.

  Definition OUTFP_sn (y w p fl t : Z) : M (list Z) Z :=
    o <- mget ;;
    match fmt_fp' o y w p fl t with
    | Some (o1, r) => if zlength o1 <=? SN_CAP then (mput o1 ;;; mret r) else munr
    | None => munr
    end.
End SnSink.

Definition TOPOK_none (sp : Z) : Prop := True.

Section StderrSink.
  Context {St : Type}.
  Variable B : Z.

  Definition SINK_stderr (m : mem) (bs : list Z * St) : Prop :=
    let buf := fst bs in
    exists (flags mode : word) (tail : list byte) (rest : list byte),
      rw_cells rsegs m RSTDERR (file_cells flags (B + 80) (B + zlength buf) B F_STDIO_WRITE B 80 2 mode 0xffffffff tail)
      /\ Z.land (bv_unsigned flags) 32 = 0 /\ Z.land (bv_unsigned flags) 8 = 0
      /\ rw_cells rsegs m B [CB 80 (zb buf ++ rest)]
      /\ zlength buf + zlength rest = 80
      /\ B + 80 < 2^63 /\ GLOBALS_TOP <= B.

  Definition OUT_stderr (s : list Z) : M (list Z * St) unit :=
    fun bs => let '(buf, st) := bs in
      if INTERNAL_BUFSIZ - zlength buf <? zlength s
      then ebind (stdio_writev 2 buf s st) (fun r => ITree.Ret (Ok (tt, ([], snd r))))
      else ITree.Ret (Ok (tt, (buf ++ s, st))).
  Definition OUTFP_stderr (y w p fl t : Z) : M (list Z * St) Z := fun _ => ITree.Ret Unr.
End StderrSink.

Section StdoutSink.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition SINK_stdout (m : mem) (st : St) : Prop :=
    let so := get_so st in
    so_active so = true /\
    exists (flags mode : word) (tail bufbytes : list byte),
      rw_cells rsegs m RSTDOUT
        (file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF
           (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
           RSTDOUT_BUF 1024 1 mode
           (if so_lbf_nl so then 10 else 0xffffffff) tail)
      /\ Z.land (bv_unsigned flags) 104 = 0
      /\ rw_cells rsegs m RSTDOUT_BUF [CB 1024 bufbytes]
      /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
      /\ zlength (so_buf so) <= 1024.
  Definition OUTFP_stdout (y w p fl t : Z) : M St Z := fun _ => ITree.Ret Unr.
End StdoutSink.

Definition stderr_wfile (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells rsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x23a98 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0.
Lemma stderr_wfile_file : forall m, stderr_wfile m -> stderr_file m.
Proof. intros m (flags & mode & e & wend & tail & H & _). exists flags, mode, e, wend, tail. exact H. Qed.

Definition fwritex_stderr_stmt : Prop :=
  forall (St : Type) (B : Z),
    @out_stmt (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr.

Definition fwritex_stdout_stmt : Prop :=
  forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
    (forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
    @out_stmt St RSTDOUT RSTDOUT_BUF 1024 (SINK_stdout get_so) TOPOK_none (stdout_fwritex get_so set_so).

Definition stdio_write_flush_post {St : Type} (B : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
  fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (B, B + 80)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ SINK_stderr B m' ([], st')
    /\ ssp_cells m' canary.
Definition stdio_write_flush_stmt : Prop :=
  forall (St : Type) (B : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list Z) (st : St) (lo : Z) (canary : word),
    SINK_stderr B m (buf, st) ->
    a0 = Z_to_bv 64 RSTDERR -> a2 = Z_to_bv 64 0 ->
    stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) -> (B + 80 <= lo \/ bv_unsigned sp <= B) ->
    ssp_cells m canary -> mem_inv rsegs m ->
    implM rsegs (stdio_writev 2 buf [] : M St unit) st
          (stdio_write_flush_post B ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17764) fc None m (seg_rom rsegs)).

Definition towrite_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (flags mode : word) (wend wpos wbase writefn buf bufsize fd lbf : Z) (tail : list byte),
    rw_cells rsegs m (bv_unsigned a0) (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv rsegs m ->
    evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned a0, bv_unsigned a0 + 232)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ rw_cells rsegs m' (bv_unsigned a0) (file_cells flags (buf + bufsize) buf buf writefn buf bufsize fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xac850) fc None m (seg_rom rsegs)).

Definition SPRINTF_DEPTH : Z := 5936.

Definition FMT_G_RET : Prop :=
  forall d prec o l, (prec = 15 \/ prec = 17) -> fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) -> l = zlength o.
Definition FMT_G_LEN25 : Prop :=
  forall d prec o l, (prec = 15 \/ prec = 17) -> fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) -> zlength o <= 25.

Definition sprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (NB : Z) (n : nat) (o : list Z) (r : Z) (junk : list byte) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp); (NB, NB + Z.of_nat n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' NB [CB n (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junk)]
    /\ ssp_cells m' canary.

Definition sprintf_d_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (n : nat) (junk : list byte) (lo : Z) (canary : word)
         (i : Z) (o : list Z) (r : Z),
    rw_cells rsegs m (bv_unsigned a0) [CB n junk] ->
    a1 = Z_to_bv 64 A_FMT_d ->
    bv_unsigned a2 mod 2^32 = i mod 2^32 -> (-2^31 <= i < 2^31) ->
    fmt_d i = Some (o, r) -> (length o < n)%nat -> (n <= 80)%nat ->
    stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - SPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) -> (bv_unsigned a0 + Z.of_nat n <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a0 + Z.of_nat n <= 65536 \/ GLOBALS_TOP <= bv_unsigned a0) ->
    ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
    evt rsegs (sprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a0) n o r junk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1766c) fc None m (seg_rom rsegs)).

Definition sprintf_g_stmt (prec : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (n : nat) (junk : list byte) (lo : Z) (canary : word)
         (o : list Z) (r : Z),
    FMT_G_RET -> FMT_G_LEN25 ->
    rw_cells rsegs m (bv_unsigned a0) [CB n junk] ->
    a1 = Z_to_bv 64 (if prec =? 15 then A_FMT_g15 else A_FMT_g17) -> (prec = 15 \/ prec = 17) ->
    fmt_g (bv_unsigned a2) prec = Some (o, r) ->
    fmt_fp_facts (f128_of_d (bv_unsigned a2)) 0 prec CHR_g ->
    (length o < n)%nat -> (n <= 80)%nat ->
    stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - SPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) -> (bv_unsigned a0 + Z.of_nat n <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a0 + Z.of_nat n <= 65536 \/ GLOBALS_TOP <= bv_unsigned a0) ->
    ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
    evt rsegs (sprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a0) n o r junk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1766c) fc None m (seg_rom rsegs)).

Definition hex4_lower (c : Z) : list Z :=
  let hd v := znth [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 97; 98; 99; 100; 101; 102] v in
  [hd ((c / 4096) mod 16); hd ((c / 256) mod 16); hd ((c / 16) mod 16); hd (c mod 16)].
Definition sprintf_u04x_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (n : nat) (junk : list byte) (lo : Z) (canary : word) (c : Z),
    rw_cells rsegs m (bv_unsigned a0) [CB n junk] ->
    a1 = Z_to_bv 64 A_FMT_u04x ->
    bv_unsigned a2 mod 2^32 = c -> (0 <= c < 256) ->
    (6 <= n)%nat -> (n <= 80)%nat ->
    stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - SPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) -> (bv_unsigned a0 + Z.of_nat n <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a0 + Z.of_nat n <= 65536 \/ GLOBALS_TOP <= bv_unsigned a0) ->
    ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
    evt rsegs (sprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a0) n (117 :: hex4_lower c) 5 junk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1766c) fc None m (seg_rom rsegs)).

Definition EMIT_DEPTH : Z := 5632.
Section Emit.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition emit_printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition emit_printf_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z) (slack : list byte),
      (forall x so, get_so (set_so so x) = so) -> (forall x so so', set_so so' (set_so so x) = set_so so' x) ->
      fwritex_stdout_stmt ->
      stdout_file m (get_so st) ->
      bytes_at rsegs m (bv_unsigned a1) (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256) s ->
      ((- (bv_unsigned a1 + zlength s + 1)) mod 8 <= zlength slack) -> (zlength s < INT_MAX) ->
      stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      (bv_unsigned a1 + zlength s + 1 + zlength slack <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      (0 < bv_unsigned a1) -> (bv_unsigned a1 + zlength s + 1 + zlength slack <= 65536 \/ GLOBALS_TOP <= bv_unsigned a1) ->
      ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
      implM rsegs (s_emit get_so set_so s) st
            (emit_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13219) fc None m (seg_rom rsegs)).

  Definition FPRINTF_DEPTH : Z := 5632.

  Definition diag_args (d : diag_msg) (m : mem) (fmtp argw : word) (lo sp : Z) : Prop :=
    match d with
    | DUsage s | DCannotOpen s | DReadError s =>
        fmtp = Z_to_bv 64 (match d with DUsage _ => A_FMT_usage | DCannotOpen _ => A_FMT_cannot_open | _ => A_FMT_read_error end)
        /\ exists slack : list byte,
             bytes_at rsegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
             /\ Forall (fun c => 0 < c < 256) s
             /\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
             /\ (zlength s < INT_MAX - 256)
             /\ (bv_unsigned argw + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned argw)
             /\ (GLOBALS_TOP <= bv_unsigned argw)
    | DTooBig => fmtp = Z_to_bv 64 A_FMT_too_big /\ bv_unsigned argw mod 2^32 = 67108864
    | _ => False
    end.

  Definition fprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary
      /\ st' = st.

  Definition fprintf_diag_stmt : Prop :=
    forall (d : diag_msg)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      fwritex_stderr_stmt -> stdio_write_flush_stmt ->
      stderr_wfile m ->
      a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
      stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
      implM rsegs (s_diag (St:=St) d) st
            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17094) fc None m (seg_rom rsegs)).
End Emit.

Example fmt_g_ret_probe1 : exists o l, fmt_fp [] (f128_of_d 0x3fb999999999999a) 1 17 0 CHR_g = Some (o, l) /\ l = zlength o /\ zlength o <= 25.
Proof. eexists _, _. split; [vm_compute; reflexivity|]. split; [reflexivity | cbv; discriminate]. Qed.
Example fmt_g_ret_probe2 : exists o l, fmt_fp [] (f128_of_d 0x8000000000000001) 1 17 0 CHR_g = Some (o, l) /\ l = zlength o /\ zlength o <= 25.
Proof. eexists _, _. split; [vm_compute; reflexivity|]. split; [reflexivity | cbv; discriminate]. Qed.
Example fmt_g_ret_probe3 : exists o l, fmt_fp [] (f128_of_d 0x7e37e43c8800759c) 1 15 0 CHR_g = Some (o, l) /\ l = zlength o /\ zlength o <= 25.
Proof. eexists _, _. split; [vm_compute; reflexivity|]. split; [reflexivity | cbv; discriminate]. Qed.
