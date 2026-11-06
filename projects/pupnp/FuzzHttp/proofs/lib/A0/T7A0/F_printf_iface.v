(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio Printf_model.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Shadow Contracts IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import Stdio_base Printf_lib F_pop_arg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition OUT_DEPTH : Z := 4160.
Definition PC_DEPTH : Z := 9280.
Definition VF_DEPTH : Z := 9648.
Definition GLOBALS_TOP : Z := 0x609000.
Definition STATIC_SPLIT : Z := 0x213e0.

Definition RO_LO : Z := 0x10000.
Definition RO_SZ : Z := 0x113e0.

Section Sink.
  Context {HC : HasCeiling} {St : Type}.
  Variables (Fp B BS : Z).
  Variable SINK : mem -> St -> Prop.
  Variable TOPOK : Z -> Prop.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

  Definition SR : list (Z * Z) := [(Fp, Fp + 232); (B, B + BS)].

  Definition sink_frame_stmt : Prop :=
    forall (W : list (Z * Z)) (m m' : mem) (st : St),
      SINK m st -> munch W m m' -> wmono asegs m m' ->
      Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv) W ->
      Forall (fun iv => snd iv <= B \/ B + BS <= fst iv) W ->
      SINK m' st.

  Definition sink_flags_stmt : Prop :=
    forall m st, SINK m st -> exists fl : byte, rw_cells asegs m Fp [CB 1 [fl]] /\ Z.land (bv_unsigned fl) 32 = 0.

  Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.

  Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (S : Z) (bs : list Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ bytes_at asegs m' S (zb bs)
      /\ asan_env asegs m'.

  Definition out_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (bs : list Z) (lo : Z) (canary : word),
      SINK m st ->
      bytes_at asegs m (bv_unsigned a0) (zb bs) ->
      Forall (fun c => 0 <= c < 256) bs -> zlength bs < 2^23 ->
      a1 = Z_to_bv 64 (zlength bs) ->
      a2 = Z_to_bv 64 Fp ->
      stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) -> (alloc_ceiling <= lo) ->
      (bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
      (bv_unsigned a0 + zlength bs < 2^47) ->
      ssp_cells m canary ->
      mem_inv asegs m ->
      asan_env asegs m -> shw m (bv_unsigned a0) (zlength bs) -> shw m B BS ->
      (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= alloc_ceiling \/ bv_unsigned sp <= B) ->
      (bv_unsigned a0 + zlength bs <= alloc_ceiling \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength bs <= Fp \/ Fp + 232 <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength bs <= B \/ B + BS <= bv_unsigned a0) ->
      implM asegs (OUT bs) st
            (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) bs lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x9af84) fc None m (seg_rom asegs)).

  Definition fpcall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ asan_env asegs m'.

  Definition fpcall_stmt (c : Z * Z * Z * Z * Z) : Prop :=
    let '(y, w, p, fl, t) := c in
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      SINK m st ->
      y = bv_unsigned a1 + 2^64 * bv_unsigned a2 ->
      a0 = Z_to_bv 64 Fp -> a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t ->
      bv_unsigned a7 <> 5 ->
      (-2^31 <= w <= 1) -> (-2^31 <= p < 2^20) -> (0 <= fl < 2^32) -> (0 <= t < 256) -> Z.lor t 32 <> 97 ->
      stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FMT_FP_DEPTH) -> (GLOBALS_TOP <= lo) -> (alloc_ceiling <= lo) ->
      (bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary ->
      mem_inv asegs m -> frm0 fc ->
      asan_env asegs m -> shw m lo (bv_unsigned sp - lo) -> shw m B BS -> shw m RO_LO RO_SZ ->
      (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= alloc_ceiling \/ bv_unsigned sp <= B) ->
      implM asegs (OUTFP y w p fl t) st
            (fpcall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x9c52c) fc None m (seg_rom asegs)).

  Definition arg_ok (m : mem) (lo sp ap : Z) (slot : word) (a : parg) : Prop :=
    match a with
    | PA_s s => exists slack : list byte,
        bytes_at asegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
        /\ Forall (fun c => 0 < c < 256) s
        /\ zlength s < 2^23
        /\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
        /\ 0 < bv_unsigned slot
        /\ bv_unsigned slot + zlength s + 1 < 2^47
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= alloc_ceiling \/ sp <= bv_unsigned slot)
        /\ shw m (bv_unsigned slot) (zlength s + 1)
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
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch ((lo, bv_unsigned sp) :: (AP, AP + 8) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ rw_cells asegs m' AP [C8 apv]
      /\ (0 <= r <= INT_MAX)
      /\ asan_env asegs m'.

  Definition printf_core_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word)
           (fmt : list Z) (VA i : Z) (slots : list word) (args : list parg),
      SINK m st ->
      bytes_at asegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
      a0 = Z_to_bv 64 Fp ->
      rw_cells asegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
      va_area m VA slots -> 0 <= i -> args_ok m lo (bv_unsigned sp) (bv_unsigned a2) (skipn (Z.to_nat i) slots) args ->
      Forall fpcall_stmt (fp_calls (length fmt) fmt args) ->
      stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) -> (alloc_ceiling <= lo) ->
      (bv_unsigned sp < 2^47) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->

      asan_env asegs m -> shw m lo (bv_unsigned sp - lo) -> shw m B BS -> shw m (bv_unsigned a1) (zlength fmt) -> shw m RO_LO RO_SZ ->

      (bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> (0 <= BS) ->
      ((699760 <= Fp /\ Fp + 232 <= 6318512) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
      ((6318520 <= B /\ B + BS <= alloc_ceiling) \/ (bv_unsigned a2 + 8 <= B /\ B + BS <= VA)) ->
      (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      implM asegs (printf_model OUT OUTFP fmt args) st
            (printf_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x9b4f4) fc None m (seg_rom asegs)).
End Sink.

Definition printf_core1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary.

Definition printf_core1_stmt {HC : HasCeiling} : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (fmt : list Z),
    bytes_at asegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
    pass1_ok fmt = true ->
    a0 = Z_to_bv 64 0 ->
    stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) -> (alloc_ceiling <= lo) ->
    (bv_unsigned sp < 2^47) ->
    ssp_cells m canary -> mem_inv asegs m ->
    (bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) ->
    (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 2^64) ->
    evt asegs (printf_core1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9b4f4) fc None m (seg_rom asegs)).

Definition TOPOK_none (sp : Z) : Prop := True.

Section StderrSink.
  Context {HC : HasCeiling} {St : Type}.
  Variable B : Z.

  Definition SINK_stderr (m : mem) (bs : list Z * St) : Prop :=
    let buf := fst bs in
    exists (flags mode : word) (tail : list byte) (rest : list byte),
      rw_cells asegs m RSTDERR (file_cells flags (B + 80) (B + zlength buf) B F_STDIO_WRITE B 80 2 mode 0xffffffff tail)
      /\ Z.land (bv_unsigned flags) 32 = 0 /\ Z.land (bv_unsigned flags) 8 = 0
      /\ rw_cells asegs m B [CB 80 (zb buf ++ rest)]
      /\ zlength buf + zlength rest = 80
      /\ B + 80 < 2^47 /\ alloc_ceiling <= B.

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
      rw_cells asegs m RSTDOUT
        (file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF
           (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
           RSTDOUT_BUF 1024 1 mode
           (if so_lbf_nl so then 10 else 0xffffffff) tail)
      /\ Z.land (bv_unsigned flags) 104 = 0
      /\ rw_cells asegs m RSTDOUT_BUF [CB 1024 bufbytes]
      /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
      /\ zlength (so_buf so) <= 1024.
  Definition OUTFP_stdout (y w p fl t : Z) : M St Z := fun _ => ITree.Ret Unr.
End StdoutSink.

Definition stderr_wfile (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x607078 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0.
Lemma stderr_wfile_file : forall m, stderr_wfile m -> stderr_file m.
Proof. intros m (flags & mode & e & wend & tail & H & _). exists flags, mode, e, wend, tail. exact H. Qed.

Section Hyps.
Context {HC : HasCeiling}.

Definition fwritex_stderr_stmt : Prop :=
  forall (St : Type) (B : Z),
    @out_stmt HC (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr.

Definition fwritex_stdout_stmt : Prop :=
  forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
    (forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
    @out_stmt HC St RSTDOUT RSTDOUT_BUF 1024 (SINK_stdout get_so) TOPOK_none (stdout_fwritex get_so set_so).

Definition stdio_write_flush_post {St : Type} (B : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
  fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (B, B + 80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ SINK_stderr B m' ([], st')
    /\ ssp_cells m' canary.
Definition stdio_write_flush_stmt : Prop :=
  forall (St : Type) (B : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list Z) (st : St) (lo : Z) (canary : word),
    SINK_stderr B m (buf, st) ->
    a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 ->
    stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp <= 2^47) -> (B + 80 <= lo \/ bv_unsigned sp <= B) ->
    ssp_cells m canary -> mem_inv asegs m ->
    implM asegs (stdio_writev 2 buf [] : M St unit) st
          (stdio_write_flush_post B ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9a800) fc None m (seg_rom asegs)).

Definition towrite_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (flags mode : word) (wend wpos wbase writefn buf bufsize fd lbf : Z) (tail : list byte),
    rw_cells asegs m (bv_unsigned a0) (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned a0, bv_unsigned a0 + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ rw_cells asegs m' (bv_unsigned a0) (file_cells flags (buf + bufsize) buf buf writefn buf bufsize fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9b174) fc None m (seg_rom asegs)).

End Hyps.

Definition EMIT_DEPTH : Z := 17920.

Definition FPRINTF_DEPTH : Z := 13744.
