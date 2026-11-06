(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Q13u Qc6I QJFf QVsB QCiC Qpj5 QCNF QoNr QdZp Qk8e Qu3b QnRU QteI QMPy QIG5 QJBH QHig QwAs Q0Do Q6sh QKTr QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho QYyZ QFd5 QlES QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp Qk8e.Mq0.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0.
Import QMPy. Import Qu3b.Mq0.
Import QIG5. Import QJBH.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QYyZ.Mq2 QFd5.Mq0 QteI.Mq2.
Import QlES.
Import QXE1.Mq0.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Definition OUT_DEPTH : Z := 3264.
Definition PC_DEPTH : Z := 5184.
Definition VF_DEPTH : Z := 5552.
Definition GLOBALS_TOP {BAND : Band} : Z := band_lo.
Definition STATIC_SPLIT : Z := 0x23fc0.

Section Sink.
Context {BAND : Band}.
Context {St : Type}.
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
Forall (fun iv => GLOBALS_TOP <= fst iv) W ->
SINK m' st.

Definition sink_flags_stmt : Prop :=
forall m st, SINK m st -> exists fl : byte, rw_cells asegs m Fp [CB 1 [fl]] /\ Z.land (bv_unsigned fl) 32 = 0 /\ ISH m.

Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.

Definition sink_ish_stmt : Prop := forall m st, SINK m st -> ISH m.

Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S : Z) (bs : list Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at asegs m' S (zb bs).

Definition out_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (bs : list Z) (lo : Z) (canary : word),
SINK m st ->
bytes_at asegs m (bv_unsigned a0) (zb bs) ->
Forall (fun c => 0 <= c < 256) bs -> zlength bs < 2^31 ->
szone (bv_unsigned a0) (zlength bs) ->
a1 = Z_to_bv 64 (zlength bs) ->
a2 = Z_to_bv 64 Fp ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv asegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
(bv_unsigned a0 + zlength bs <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= Fp \/ Fp + 232 <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= B \/ B + BS <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= 2^47) ->
implM asegs (OUT bs) st
(out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) bs lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd33c8) fc None m (seg_rom asegs)).

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
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FMT_FP_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv asegs m -> frm0 fc ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
implM asegs (OUTFP y w p fl t) st
(fpcall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd4a44) fc None m (seg_rom asegs)).

Definition arg_ok (m : mem) (lo sp ap : Z) (slot : word) (a : parg) : Prop :=
match a with
| PA_s s => exists slack : list byte,
bytes_at asegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
/\ 0 < bv_unsigned slot
/\ szone (bv_unsigned slot) (zlength s + 1)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= B \/ B + BS <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= ap \/ ap + 8 <= bv_unsigned slot)
/\ bv_unsigned slot + zlength s + 1 + zlength slack <= 2^47
| PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
| PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
| PA_g d => bv_unsigned slot = d
| PA_li i => -2^63 <= i < 2^63 /\ bv_unsigned slot = i mod 2^64
| PA_lu u => 0 <= u < 2^64 /\ bv_unsigned slot = u
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
/\ (0 <= r <= INT_MAX).

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
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->

(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> szone (bv_unsigned a1) (zlength fmt) -> (0 <= BS) ->
((945072 <= Fp /\ Fp + 232 <= 6565536) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
((6566104 <= B /\ B + BS <= lo) \/ (bv_unsigned a2 + 8 <= B /\ B + BS <= VA)) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
implM asegs (printf_model OUT OUTFP fmt args) st
(printf_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3a0c) fc None m (seg_rom asegs)).
End Sink.

Definition printf_core1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary.

Definition printf_core1_stmt {BAND : Band} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (fmt : list Z),
bytes_at asegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
pass1_ok fmt = true ->
a0 = Z_to_bv 64 0 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m ->
(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> szone (bv_unsigned a1) (zlength fmt) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 2^64) ->
evt asegs (printf_core1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3a0c) fc None m (seg_rom asegs)).

Definition TOPOK_none (sp : Z) : Prop := sp + 16 <= 2^47.

Definition OUT_MAX : Z := 16777216.

Section StderrSink.
Context {BAND : Band}.
Context {St : Type}.
Variable B : Z.

Definition SINK_stderr (m : mem) (bs : list Z * St) : Prop :=
let buf := fst bs in
exists (flags mode : word) (tail : list byte) (rest : list byte),
rw_cells asegs m RSTDERR (file_cells flags (B + 80) (B + zlength buf) B F_STDIO_WRITE B 80 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 32 = 0 /\ Z.land (bv_unsigned flags) 8 = 0
/\ rw_cells asegs m B [CB 80 (zb buf ++ rest)]
/\ zlength buf + zlength rest = 80
/\ B + 80 < 2^63 /\ GLOBALS_TOP + 64 <= B /\ B + 96 <= 2^47
/\ ISH m.

Definition OUT_stderr (s : list Z) : M (list Z * St) unit :=
fun bs => let '(buf, st) := bs in
if OUT_MAX <? zlength s then Qc6I.Ret Unr
else if INTERNAL_BUFSIZ - zlength buf <? zlength s
then ebind (stdio_writev 2 buf s st) (fun r => Qc6I.Ret (Ok (tt, ([], snd r))))
else Qc6I.Ret (Ok (tt, (buf ++ s, st))).
Definition OUTFP_stderr (y w p fl t : Z) : M (list Z * St) Z := fun _ => Qc6I.Ret Unr.
End StderrSink.

Section StdoutSink.
Context {BAND : Band}.
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
/\ zlength (so_buf so) <= 1024
/\ ISH m.
Definition OUTFP_stdout (y w p fl t : Z) : M St Z := fun _ => Qc6I.Ret Unr.

Definition OUT_stdout (s : list Z) : M St unit :=
if OUT_MAX <? zlength s then munr else stdout_fwritex get_so set_so s.
End StdoutSink.

Definition stderr_wfile (m : mem) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x6435e0 0 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 40 = 0.

Definition fwritex_stderr_stmt {BAND : Band} : Prop :=
forall (St : Type) (B : Z),
@out_stmt _ (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr.

Definition fwritex_stdout_stmt {BAND : Band} : Prop :=
forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
(forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
@out_stmt _ St RSTDOUT RSTDOUT_BUF 1024 (SINK_stdout get_so) TOPOK_none (OUT_stdout get_so set_so).

Definition stdio_write_flush_post {BAND : Band} {St : Type} (B : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (B, B + 80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK_stderr B m' ([], st')
/\ ssp_cells m' canary.
Definition stdio_write_flush_stmt {BAND : Band} : Prop :=
forall (St : Type) (B : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list Z) (st : St) (lo : Z) (canary : word),
SINK_stderr B m (buf, st) ->
a0 = Z_to_bv 64 RSTDERR -> a2 = Z_to_bv 64 0 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> (B + 80 <= lo \/ bv_unsigned sp <= B) ->
ssp_cells m canary -> mem_inv asegs m ->
bv_unsigned a1 <= 2^47 ->
implM asegs (stdio_writev 2 buf [] : M St unit) st
(stdio_write_flush_post B ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd29d0) fc None m (seg_rom asegs)).

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
F (Z_to_bv 64 0xd3374) fc None m (seg_rom asegs)).

Definition EMIT_DEPTH : Z := 5728.
Section Emit.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition emit_printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stdout_file m' (get_so st')
/\ ssp_cells m' canary.

Definition emit_printf_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (v : Z),
(forall x so, get_so (set_so so x) = so) -> (forall x so so', set_so so' (set_so so x) = set_so so' x) ->
fwritex_stdout_stmt ->
stdout_file m (get_so st) -> ISH m ->
(-2^31 <= v < 2^31) -> (bv_unsigned a1 mod 2^32 = v mod 2^32) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_emit get_so set_so v) st
(emit_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91a50) fc None m (seg_rom asegs)).

Definition FPRINTF_DEPTH : Z := 5664.

Definition AFMT_emit_d : Z := 0x14e05.      Definition AFMT_usage : Z := 0x1610a.
Definition AFMT_too_big : Z := 0x1a7dd.     Definition AFMT_cannot_open : Z := 0x1edde.
Definition AFMT_read_error : Z := 0x1edf3.

Definition diag_args (d : diag_msg) (m : mem) (fmtp argw : word) (lo sp : Z) : Prop :=
match d with
| DUsage s | DCannotOpen s | DReadError s =>
fmtp = Z_to_bv 64 (match d with DUsage _ => AFMT_usage | DCannotOpen _ => AFMT_cannot_open | _ => AFMT_read_error end)
/\ exists slack : list byte,
bytes_at asegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
/\ (zlength s <= OUT_MAX)
/\ (bv_unsigned argw + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned argw)
/\ (GLOBALS_TOP + 64 <= bv_unsigned argw) /\ (bv_unsigned argw + zlength s + 9 <= 2^47)
/\ (bv_unsigned argw + zlength s + 1 + zlength slack <= 2^47)
| DTooBig => fmtp = Z_to_bv 64 AFMT_too_big /\ bv_unsigned argw mod 2^32 = 67108864
| _ => False
end.

Definition fprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile m'
/\ ssp_cells m' canary
/\ st' = st.

Definition fprintf_diag_stmt : Prop :=
forall (d : diag_msg)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
fwritex_stderr_stmt -> stdio_write_flush_stmt ->
stderr_wfile m -> ISH m ->
a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_diag (St:=St) d) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4f998) fc None m (seg_rom asegs)).
End Emit.

End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 QDM6 Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Qc27 Q13u QDM6 QHig QwAs.Mq2 Q0Do.
Import QCiC.Mq1 Q6sh QKTr.
Import Qu3b.Mq3. Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq1 Qu3b.Mq1 QYyZ.Mq2 QnRU.Mq3 QteI.Mq1.
Import Q0z1.
Import QlES.
Import QXE1.Mq0.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_6 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells asegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Definition sn_write_entry : Z := 0xd90d0.
Definition SN_WRITE_STACK : Z := (64 + MEMCPY_ICPT_STACK)%Z.

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
/\ rw_cells asegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junk)]
/\ rw_cells asegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
/\ rw_cells asegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
/\ bytes_at asegs m' B (zb o).

Lemma sn_write_spec {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (lo : Z),
a0 = Z_to_bv 64 Fp -> a2 = Z_to_bv 64 0 ->
rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
rw_cells asegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
bytes_at asegs m B (zb o) ->
rw_cells asegs m D [CB dn junk] -> (length o < dn)%nat -> (zlength o <= n < 2^63)%Z -> (0 <= bufp < 2^64)%Z -> (B + zlength o < 2^63)%Z ->
stk asegs m lo (bv_unsigned sp) -> (band_lo <= lo)%Z -> (lo <= bv_unsigned sp - SN_WRITE_STACK)%Z -> mem_inv asegs m ->

(B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z ->
(CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z ->
(Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z ->
(D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D)%Z ->
(bv_unsigned sp <= CK)%Z -> (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
(CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z ->
(B + zlength o <= CK \/ CK + 16 <= B)%Z -> (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z ->

shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m B (zlength o) -> ((0 < zlength o)%Z -> rng_ok m D (zlength o)) ->
evt asegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D n B bufp o dn junk lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd90d0) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros -> -> WPOS WBASE BUF COOKIE CKC SRC DST ROOM Hn Hbufp BHI ST CEIL LO MI D1 D2 D3 D4 S1 S2 S3 S4 S5 S6 SB RC RS RD.
pose proof CEIL as CEIL'. unfold SN_WRITE_STACK, MEMCPY_ICPT_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
pose proof (bytes_at_bound _ _ _ _ SRC) as BB. pose proof (zb_length o) as LZ. rewrite LZ in BB. unfold zlength in *.
pose proof (munch_refl [(lo, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUs.
pose proof (wmono_refl asegs m) as WM.
pose_word_ranges.
carve_frame 64%nat ST.
do 15 zs.
zs. replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
zs. zs. brf K1; [exfalso; lia|]. zs. zs. zs. brf K2.
-
clear MUs.
assert (O0 : length o = 0%nat) by lia. destruct o as [|c o']; [|cbn in O0; lia]. cbn [length Z.of_nat] in *.
zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
pose proof (rw_CB_length _ _ _ _ DST) as LJ.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST.
zs. zs. zs. zs.
do 9 zs.
match goal with STa : stk asegs ?mc lo (bv_unsigned sp + -64)%Z, FRx : rw_cells asegs ?mc (bv_unsigned sp + -64)%Z _ |- _ => release_frame FRx STa (bv_unsigned sp) end.
apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
split. { cbn [zlength length Z.of_nat]. rewrite Z.add_0_r, Z.sub_0_r. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
split. { cbn [zb map app length skipn]. rewrite upd_firstn_skipn in DST by (rewrite LJ; lia). cbn [firstn app] in DST. exact DST. }
split; [assumption|]. split; [assumption|]. assumption.
-
pose proof (rw_CB_length _ _ _ _ DST) as LJ.
apply (rw_cells_split_CB asegs _ _ [] dn _ [] [length o; dn - length o]%nat) in DST; [ | cbn; lia ].
cbn [mk_CB_cells app] in DST.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb]. cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
zs. zs.

specialize (RD ltac:(lia)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SB1;
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RC1;
assert (RS1 : rng_ok mc B (Z.of_nat (length o)))
by (eapply rng_ok_munch; [exact RS| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RS)); Z.div_mod_to_equations; lia);
assert (RD1 : rng_ok mc D (Z.of_nat (length o)))
by (eapply rng_ok_munch; [exact RD| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RD)); Z.div_mod_to_equations; lia)
end.
clear MUs.
call_u (memcpy_icpt_spec D B (Z.of_nat (length o)) lo (zb o) (firstn (length o) junk));
[ exact SRC| rewrite LZ, Nat2Z.id; reflexivity| rewrite Nat2Z.id; exact DSTa| lia| assumption| lia
| unsigned_lits; eassumption| exact CEIL| unsigned_lits; unfold MEMCPY_ICPT_STACK; lia| unsigned_lits; lia| unsigned_lits; lia
| exact SB1| exact RC1| exact RS1| exact RD1|].
rewrite ?(unsigned_lit D), ?(unsigned_lit B), ?(unsigned_lit (Z.of_nat (length o))) in * by lia.
rewrite !Nat2Z.id in *.
match goal with MC : rw_cells _ _ D [CB (length o) (zb o)] |- _ => rename MC into DSTa' end.
zs. zs. zs. zs. zs. zs.
zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
pose proof (rw_CB_length _ _ _ _ DSTb) as LJb.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTb) as DA. clear DSTb.
pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 (D + Z.of_nat (length o))) DA ltac:(rewrite LJb; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length o))) with (wa (D + Z.of_nat (length o) + 0)) by (unfold wa; f_equal; lia).
pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJb; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTb. rewrite upd_length, LJb in DSTb.
zs. zs. zs. zs.
do 9 zs.
match goal with STa : stk asegs ?mc lo (bv_unsigned sp + -64)%Z, FRx : rw_cells asegs ?mc (bv_unsigned sp + -64)%Z _ |- _ => release_frame FRx STa (bv_unsigned sp) end.
apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split. { unfold zlength. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
split.
{ match goal with Ha : rw_cells _ ?mm D [CB _ ?l1], Hb : rw_cells _ ?mm (D + _)%Z [CB _ ?l2] |- _ =>
assert (J : rw_cells asegs mm D ([] ++ [CB (length o) l1; CB (dn - length o) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact Hb
| apply rw_cells_merge in J; cbn [cells_size cells_bytes csize cbytes app] in J; rewrite app_nil_r in J ] end.
replace (length o + (dn - length o + 0))%nat with dn in J by lia.
rewrite upd_firstn_skipn in J by (rewrite length_firstn, length_skipn, LJ; lia). change (Z.to_nat 0) with 0%nat in J. rewrite firstn_O, app_nil_l in J.
rewrite skipn_firstn_comm, skipn_skipn in J. replace (1 + length o)%nat with (S (length o)) in J by lia.
rewrite firstn_all2 in J by (rewrite length_skipn, LJ; lia). first [exact J | let t := type of J in idtac "J:" t; match goal with |- ?g => idtac g end; fail]. }
split; [assumption|]. split; [assumption|]. assumption.
Qed.
End Mq1.
From Stdlib Require String Ascii.
From stdpp Require gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1.
Import Q0z1.
Import QlES.
Import QXE1.Mq0.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Ltac addr_diff E A ::=
let k :=
lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end in
let ok := eval vm_compute in (Z.ltb k 65536) in
lazymatch ok with true => k end. Ltac mkr__addr_diff_3 E A := let k :=
lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end in
let ok := eval vm_compute in (Z.ltb k 65536) in
lazymatch ok with true => k end.

Ltac has_var c := match c with context [?x] => is_var x end.
Ltac bif := try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
tryif has_var c then idtac else
(let v := eval vm_compute in c in
lazymatch v with
| true => replace c with true by (vm_compute; reflexivity); cbv iota
| false => replace c with false by (vm_compute; reflexivity); cbv iota
end) end).

Ltac subfix := repeat match goal with |- context [Z_to_bv 64 (?x - ?k)] => is_Zlit k; let nk := eval vm_compute in (- k)%Z in replace (x - k)%Z with (x + nk)%Z by lia end.
Lemma zx8_lit : forall e, 0 <= e < 2^64 -> zx8 (Z_to_bv 64 e) = Z_to_bv 64 (e mod 256).
Proof. intros e He. unfold zx8. rewrite unsigned_lit by lia. reflexivity. Qed.

Ltac bnorm :=
repeat match goal with
| |- context [zx8 (Z_to_bv 64 ?e)] => is_Zlit e; rewrite (zx8_lit e) by lia;
let v := eval vm_compute in (e mod 256)%Z in change (e mod 256)%Z with v
| |- context [bv_unsigned (Z_to_bv 64 ?e)] => is_Zlit e;
let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 e)) in change (bv_unsigned (Z_to_bv 64 e)) with v
end.
Ltac bstep := istep; subfix; bnorm; bif.

Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstep end).

Definition pcommon_entry : Z := 0x533cc.
Definition PCOMMON_STACK : Z := 2320.

Definition S_diouxXn : Z := 0x1d915.  Definition S_float : Z := 0x16c7d.  Definition S_flags : Z := 0x15b57.
Definition S_lenmod : Z := 0x1c640.   Definition S_cCsS : Z := 0x146d7.   Definition S_CS : Z := 0x1abb9.
Definition S_csb : Z := 0x1086e.      Definition S_sS : Z := 0x13f97.     Definition K_aa : Z := 0x10460.

Lemma lor_range64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
intros a b Ha Hb. pose proof (Z.lor_nonneg a b).
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
split; [lia|]. apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 64 ltac:(lia))).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|Na]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 a 64 ltac:(lia))). lia.
- destruct (Z.eq_dec b 0) as [->|Nb]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 b 64 ltac:(lia))). lia.
Qed.
Lemma lor40_and15 : forall x, Z.land (Z.lor 40 x) 15 <> 0.
Proof.
intros x E. apply (f_equal (fun z => Z.testbit z 3)) in E.
rewrite Z.land_spec, Z.lor_spec, Z.bits_0 in E. cbn in E. discriminate.
Qed.

Definition imemset_bpost (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (d n cur : Z) (k : nat) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + n)) (wz (d + n)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(cur, d + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' cur [CB k (repeat (b8 0) k)].

Lemma imemset_bloop : forall (k : nat) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (d n cur : Z) (rest : list byte),
rw_cells asegs m cur [CB k rest] -> mem_inv asegs m ->
cur + Z.of_nat k = d + n -> (0 < k)%nat -> 0 <= d -> d <= cur -> d + n < 2^64 ->
evt asegs (imemset_bpost ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d n cur k m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + n)) (wz cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x74f88) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until rest; intros DST MI HK K0 D0 DC DN; [lia|].
assert (LR : length rest = S k) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
pose proof (munch_refl [(cur, d + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] (S k) rest [] [1%nat; k]) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
step. change (bv_unsigned (wz 0)) with 0 in DST.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [B0 DST]. cbn [cells_size csize Nat.add Z.of_nat] in DST.
step. step.
destruct k as [|k'].
-
ifF. step. step.
apply evt_done. unfold imemset_bpost. exists m0.
replace (cur + 1) with (d + n) by lia.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
eapply rw_cells_recast'; [exact B0| cbn; split; [reflexivity| exact I]| reflexivity].
- ifT. replace (Z.pos (Pos.of_succ_nat 0)) with 1 in DST by reflexivity.
replace (Z.pos (Pos.of_succ_nat 0)) with 1 in DST by reflexivity.
eapply evt_mono; [eapply (IH ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 d n (cur + 1)); [exact DST| exact MI| lia| lia| lia| lia| lia] |].
cbv beta. intros ms' (m' & -> & MU2 & WM2 & MI2 & Z2). unfold imemset_bpost. exists m'.
split; [reflexivity|].
split. { apply (munch_trans _ m m0 m'); [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn; intros; lia. }
split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|].
assert (B0' : rw_cells asegs m' cur [C1 (b8 0)]).
{ eapply rw_cells_apart; [exact B0| exact MU2| exact WM2|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
pose proof (proj2 (rw_cells_app asegs m' cur [C1 (b8 0)] [CB (S k') (repeat (b8 0) (S k'))]) (conj B0' Z2)) as J.
eapply rw_cells_recast'; [exact J| cbn; split; [| exact I]; cbn; rewrite repeat_length; reflexivity| reflexivity].
Qed.

Definition imemset40_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (d : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + 40)) (wz (d + 40)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(d, d + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' d [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].

Lemma imemset40_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (d : Z) (cs : list cell),
rw_cells asegs m d cs -> cells_size cs = 40%nat -> mem_inv asegs m -> d + 40 < 2^64 ->
evt asegs (imemset40_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz 40) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x74f70) fc None m (seg_rom asegs)).
Proof.
intros until cs; intros DST SZ MI DN.
pose proof (rw_cells_bound _ _ _ _ DST) as BD. rewrite SZ in BD. cbn in BD.
pose proof (rw_cells_merge asegs m d [] cs [] ltac:(cbn [app]; rewrite app_nil_r; exact DST)) as D40.
cbn [app] in D40. rewrite SZ in D40.
assert (L15 : 0 < Z.land (Z.lor 40 d) 15 < 16).
{ pose proof (lor40_and15 d). split; [pose proof (Z.land_nonneg (Z.lor 40 d) 15); lia|].
change 16 with (2^4). replace 15 with (Z.ones 4) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
step. step. rewrite ?(unsigned_lit d) by lia. rewrite (unsigned_lit (Z.lor 40 d)) by (apply lor_range64; lia).
step. ifz. step. ifz. step. step.
eapply evt_mono; [eapply (imemset_bloop 40 ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d 40 d); [exact D40| exact MI| lia| lia| lia| lia| lia] |].
cbv beta. intros ms' (m' & -> & MU & WM & MI' & Z40). unfold imemset40_post. exists m'.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
eapply rw_cells_recast'; [exact Z40| cbn; repeat split; exact I| reflexivity].
Qed.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_nth : forall (s : list Z) (t : list byte) i, 0 <= i < zlength s ->
firstn 1 (skipn (Z.to_nat i) (zb s ++ t)) = [b8 (nth (Z.to_nat i) s 0)].
Proof.
intros s t i Hi. unfold zlength in Hi. rewrite skipn_app. unfold zb. rewrite skipn_map.
replace (Z.to_nat i - length (map (λ z : Z, b8 z) s))%nat with 0%nat by (rewrite length_map; lia). cbn [skipn].
destruct (skipn (Z.to_nat i) s) as [|c rest] eqn:E.
- exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
- cbn. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat i)), <- (nth_skipn _ s 0 0%Z), E. reflexivity.
Qed.
Lemma zb_end : forall (s : list Z) (b : byte) (t : list byte), firstn 1 (skipn (Z.to_nat (zlength s)) (zb s ++ b :: t)) = [b].
Proof.
intros s b t. unfold zlength. rewrite Nat2Z.id, skipn_app. unfold zb. rewrite skipn_all2 by (rewrite length_map; lia).
rewrite length_map, Nat.sub_diag. reflexivity.
Qed.

Section IStrlen.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (p : Z) (s : list Z) (t : list byte).
Hypothesis SRC : bytes_at asegs m p (zb s ++ b8 0 :: t).
Hypothesis BYT : Forall (fun c => 0 < c < 256) s.

Definition istrlen_post : machine_state -> Prop :=
eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (zlength s)) (wz (zlength s + 1)) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)).

Lemma istrlen_loop : forall (n : nat) (i : Z) (a2 : word), Z.of_nat n = zlength s - i -> 0 <= i <= zlength s ->
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) (wz i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x750c8) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros i a2 Hn Hi.
-
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 0]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app, ?zb_length; cbn; unfold zlength in *; lia).
replace i with (zlength s) by lia. rewrite zb_end. reflexivity. }
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS. unfold zlength in *.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
change (zxb (b8 0)) with (wz 0). step. step. bif. step. step.
apply evt_done. unfold istrlen_post, zlength. replace i with (Z.of_nat (length s)) by lia. reflexivity.
- pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
assert (CR : 0 < nth (Z.to_nat i) s 0 < 256).
{ apply (proj1 (List.Forall_forall _ _) BYT). apply nth_In. unfold zlength in *; lia. }
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 (nth (Z.to_nat i) s 0)]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app, ?zb_length; cbn; unfold zlength in *; lia).
rewrite zb_nth by lia. reflexivity. }
unfold zlength in *.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
rewrite zxb_b8, Z.mod_small by lia.
step. step. ifT. apply (IH (i + 1)); lia.
Qed.

Lemma istrlen_spec : forall (a1 a2 : word),
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x750c4) fc None m (seg_rom asegs)).
Proof.
intros a1 a2. step. apply (istrlen_loop (Z.to_nat (zlength s)) 0); unfold zlength; lia.
Qed.
End IStrlen.

Fixpoint strchr_res (q : Z) (l : list Z) (c : Z) : Z :=
match l with [] => 0 | z :: l' => if z =? c then q else strchr_res (q + 1) l' c end.

Section IStrchr.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z).
Hypothesis CR : 0 < c < 256.

Definition istrchr_post (r : Z) : machine_state -> Prop :=
fun ms' => exists a1' a3' : word,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1' (wz c) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs).

Lemma istrchr_loop : forall (l : list Z) (q : Z) (t : list byte) (a1 : word),
bytes_at asegs m q (zb l ++ b8 0 :: t) -> Forall (fun z => 0 < z < 256) l -> hd 0 l <> c ->
evt asegs (istrchr_post (strchr_res q l c))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) a1 (wz c) (wz (hd 0 l)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75034) fc None m (seg_rom asegs)).
Proof.
induction l as [|z l IH]; intros q t a1 STR BYT NE.
- cbn [hd strchr_res]. step. ifT. step. step. apply evt_done. unfold istrchr_post. do 2 eexists. reflexivity.
- cbn [hd] in NE |- *. apply Forall_cons_iff in BYT. destruct BYT as [Bz BYT].
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
cbn [strchr_res]. replace (z =? c) with false by (symmetry; apply Z.eqb_neq; exact NE).
step. ifF.
assert (RD : ov_read_bytes asegs m (wa (q + 1)) 1 = Some [b8 (hd 0 l)]).
{ rewrite (bytes_at_read asegs m q _ 1 1 STR) by (rewrite ?length_app, ?zb_length; cbn; lia).
destruct l as [|z' l']; reflexivity. }
assert (CR' : 0 <= hd 0 l < 256).
{ destruct l as [|z' l']; cbn; [lia|]. apply Forall_cons_iff in BYT. lia. }
step. clear RD. rewrite zxb_b8, Z.mod_small by lia. step. step. step.
destruct (Z.eq_dec (hd 0 l) c) as [E|NE'].
+ ifF. step. step. apply evt_done. unfold istrchr_post.
destruct l as [|z' l']; cbn [hd] in E; [lia|]. cbn [strchr_res]. rewrite (proj2 (Z.eqb_eq _ _) E). do 2 eexists. reflexivity.
+ ifT. apply (IH (q + 1) t); [| exact BYT| exact NE'].
pose proof STR as STR'. change (zb (z :: l) ++ b8 0 :: t) with ([b8 z] ++ (zb l ++ b8 0 :: t)) in STR'.
apply bytes_at_app in STR'. destruct STR' as [_ S2]. cbn [length Z.of_nat Pos.of_succ_nat] in S2. exact S2.
Qed.

Lemma istrchr_spec : forall (l : list Z) (q : Z) (t : list byte) (a1 a2 a3 : word),
bytes_at asegs m q (zb l ++ b8 0 :: t) -> Forall (fun z => 0 < z < 256) l -> a1 = wz c ->
evt asegs (istrchr_post (strchr_res q l c))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75024) fc None m (seg_rom asegs)).
Proof.
intros l q t a1 a2 a3 STR BYT ->.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
assert (RD : ov_read_bytes asegs m (wa (q + 0)) 1 = Some [b8 (hd 0 l)]).
{ rewrite (bytes_at_read asegs m q _ 0 1 STR) by (rewrite ?length_app, ?zb_length; cbn; lia). destruct l; reflexivity. }
assert (CR' : 0 <= hd 0 l < 256).
{ destruct l as [|z' l']; cbn; [lia|]. apply Forall_cons_iff in BYT. lia. }
step. clear RD. rewrite zxb_b8, Z.mod_small by lia.
step. rewrite (unsigned_lit c) by lia. change (Z.land c 255) with (Z.land c (Z.ones 8)). rewrite Z.land_ones, Z.mod_small by lia.
step. destruct (Z.eq_dec (hd 0 l) c) as [E|NE].
- ifF. step. apply evt_done. unfold istrchr_post.
destruct l as [|z' l']; cbn [hd] in E; [lia|]. cbn [strchr_res]. rewrite (proj2 (Z.eqb_eq _ _) E). do 2 eexists. reflexivity.
- ifT. apply (istrchr_loop l q t); assumption.
Qed.
End IStrchr.

Definition boxed (P : Prop) : Prop := P.

Lemma rwc_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Lemma ro_str : forall m A (l : list Z), mem_inv asegs m -> ro_bytes_b asegs A (map b8 l) = true ->
0 <= A -> A + Z.of_nat (length l) <= 2^64 -> ro_cells asegs m A (map (fun z => C1 (b8 z)) l).
Proof.
intros m A l MI RB H0 HL.
pose proof (ro_cells_image asegs m A (map b8 l) MI RB H0 ltac:(rewrite length_map; exact HL)) as R.
eapply ro_cells_recast'; [exact R| |].
- clear. induction l as [|z l IH]; cbn; [exact I|]. split; [exact I| exact IH].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. clear. induction l as [|z l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma ro_img8 : forall m A v, mem_inv asegs m -> ro_bytes_b asegs A (le8 (wz v)) = true -> 0 <= A -> A + 8 <= 2^64 ->
ro_cells asegs m A [C8 (wz v)].
Proof.
intros m A v MI RB H0 HL.
pose proof (ro_cells_image asegs m A (le8 (wz v)) MI RB H0 ltac:(rewrite length_le8; exact HL)) as R.
eapply ro_cells_recast'; [exact R| cbn; split; exact I| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
Qed.

Ltac name_towers H :=
repeat match type of H with
| context [CB ?n ?j] =>
lazymatch j with
| firstn _ _ => idtac | skipn _ _ => idtac
end;
let x := fresh "jk" in set (x := j) in H; clearbody x
end.
Ltac pc_carve ST :=
carve_frame 2240%nat ST;
lazymatch goal with FR : rw_cells _ _ _ [CB 2240 _] |- _ =>
apply (rw_cells_split_CB asegs _ _ [] 2240 _ _ [2136; 104]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
name_towers FR end.

Definition pc_prologue_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (ms' : machine_state) : Prop :=
exists (m' : mem) (jk : list byte),
ms' = MS (mkR ra (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x5340c) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -2240) [CB 2136 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma pc_prologue {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> band_lo <= lo -> lo <= bv_unsigned sp - 2320 ->
evt asegs (pc_prologue_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST MI CEIL LO.
pose proof CEIL as CEIL'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold pcommon_entry.
pc_carve ST.
do 16 bstep.
apply evt_done. unfold pc_prologue_post. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

Lemma u8_lit' : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
Lemma forallb_skipn' {X} (f : X -> bool) : forall i l, forallb f l = true -> forallb f (skipn i l) = true.
Proof. induction i as [|i IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn in H |- *. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.
Lemma cells_size_mapC1 : forall l, cells_size (map (fun c => C1 (b8 c)) l) = length l.
Proof. induction l as [|c l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma ro_C1_skipn : forall segs m A l i, ro_cells segs m A (map (fun c => C1 (b8 c)) l) -> (i <= length l)%nat ->
ro_cells segs m (A + Z.of_nat i) (map (fun c => C1 (b8 c)) (skipn i l)).
Proof.
intros segs m A l i H Hi. rewrite <- (firstn_skipn i l), map_app in H. apply ro_cells_app in H. destruct H as [_ H].
rewrite cells_size_mapC1, length_firstn, Nat.min_l in H by lia. exact H.
Qed.

Lemma pc_scan_core {BAND : Band} : forall (n : nat) (l : list Z) (p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m p (map (fun c => C1 (b8 c)) l) ->
0 <= p -> p + Z.of_nat (length l) <= 2^47 -> (n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n l) = true ->
nth n l 0 = 37 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 37) a1 a2 a3 a4 a5 a6 a7 s2 (wz (p + Z.of_nat n)) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x53524) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros l p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hp Hl Hn HB HN H37 K;
(destruct l as [|c l']; [cbn in Hn; lia|]);
change (map (fun c => C1 (b8 c)) (c :: l')) with ([C1 (b8 c)] ++ map (fun c => C1 (b8 c)) l') in FM;
apply ro_cells_app in FM; destruct FM as [C0 FM]; cbn [cells_size csize Nat.add] in FM;
cbn [forallb] in HB; apply andb_prop in HB as [Hc HB]; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2.
- cbn [nth] in H37. subst c. rewrite Z.add_0_r in K.
bstep. bstep. exact K.
- cbn [firstn forallb] in HN. apply andb_prop in HN as [Hc HN]. apply andb_prop in Hc as [Hc3 Hc4].
apply Bool.negb_true_iff, Z.eqb_neq in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc4.
bstep. bstep.
if_cases K1; zify_cond K1; rewrite ?(u8_lit' c), ?unsigned_lit in K1 by lia; [exfalso; lia|].
bstep.
if_cases K2; zify_cond K2; rewrite ?(u8_lit' c), ?unsigned_lit in K2 by lia; [exfalso; lia|].
bstep. bstep. bstep.
eapply (IH l' (p + 1)); clear IH.
+ exact FM.
+ lia.
+ cbn [length] in Hl. lia.
+ cbn [length] in Hn. lia.
+ exact HB.
+ exact HN.
+ exact H37.
+ replace (p + 1 + Z.of_nat n) with (p + Z.of_nat (S n)) by lia. exact K.
Qed.

Lemma pc_scan {BAND : Band} : forall (n i : nat) (l : list Z) (A q p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m A (map (fun c => C1 (b8 c)) l) ->
q = A + Z.of_nat (i + n) -> p = A + Z.of_nat i -> 0 <= A -> A + Z.of_nat (length l) <= 2^47 -> (i + n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n (skipn i l)) = true ->
nth (i + n) l 0 = 37 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 37) a1 a2 a3 a4 a5 a6 a7 s2 (wz q) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x53524) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m (seg_rom asegs)).
Proof.
intros n i l A q p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hq -> HA Hl Hn HB HN H37 K.
eapply (pc_scan_core n (skipn i l)).
- apply ro_C1_skipn; [exact FM| lia].
- lia.
- rewrite length_skipn. lia.
- rewrite length_skipn. lia.
- apply forallb_skipn'. exact HB.
- exact HN.
- rewrite nth_skipn. exact H37.
- replace (A + Z.of_nat i + Z.of_nat n) with q by lia. exact K.
Qed.

Lemma pc_scan_nul_core {BAND : Band} : forall (n : nat) (l : list Z) (p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m p (map (fun c => C1 (b8 c)) l) ->
0 <= p -> p + Z.of_nat (length l) <= 2^47 -> (n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n l) = true ->
nth n l 0 = 0 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 (wz (p + Z.of_nat n)) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x535b4) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros l p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hp Hl Hn HB HN H0 K;
(destruct l as [|c l']; [cbn in Hn; lia|]);
change (map (fun c => C1 (b8 c)) (c :: l')) with ([C1 (b8 c)] ++ map (fun c => C1 (b8 c)) l') in FM;
apply ro_cells_app in FM; destruct FM as [C0 FM]; cbn [cells_size csize Nat.add] in FM;
cbn [forallb] in HB; apply andb_prop in HB as [Hc HB]; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2.
- cbn [nth] in H0. subst c. rewrite Z.add_0_r in K.
bstep. bstep. bstep. exact K.
- cbn [firstn forallb] in HN. apply andb_prop in HN as [Hc HN]. apply andb_prop in Hc as [Hc3 Hc4].
apply Bool.negb_true_iff, Z.eqb_neq in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc4.
bstep. bstep.
if_cases K1; zify_cond K1; rewrite ?(u8_lit' c), ?unsigned_lit in K1 by lia; [exfalso; lia|].
bstep.
if_cases K2; zify_cond K2; rewrite ?(u8_lit' c), ?unsigned_lit in K2 by lia; [exfalso; lia|].
bstep. bstep. bstep.
eapply (IH l' (p + 1)); clear IH.
+ exact FM.
+ lia.
+ cbn [length] in Hl. lia.
+ cbn [length] in Hn. lia.
+ exact HB.
+ exact HN.
+ exact H0.
+ replace (p + 1 + Z.of_nat n) with (p + Z.of_nat (S n)) by lia. exact K.
Qed.

Lemma pc_scan_nul {BAND : Band} : forall (n i : nat) (l : list Z) (A q p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m A (map (fun c => C1 (b8 c)) l) ->
q = A + Z.of_nat (i + n) -> p = A + Z.of_nat i -> 0 <= A -> A + Z.of_nat (length l) <= 2^47 -> (i + n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n (skipn i l)) = true ->
nth (i + n) l 0 = 0 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 (wz q) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x535b4) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m (seg_rom asegs)).
Proof.
intros n i l A q p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hq -> HA Hl Hn HB HN H0 K.
eapply (pc_scan_nul_core n (skipn i l)).
- apply ro_C1_skipn; [exact FM| lia].
- lia.
- rewrite length_skipn. lia.
- rewrite length_skipn. lia.
- apply forallb_skipn'. exact HB.
- exact HN.
- rewrite nth_skipn. exact H0.
- replace (A + Z.of_nat i + Z.of_nat n) with q by lia. exact K.
Qed.

Ltac scan_side A := first [ lazymatch goal with H : ro_cells _ _ A _ |- ro_cells _ _ A _ => exact H end | reflexivity | lia
| apply Z.leb_le; vm_compute; reflexivity | apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity ].
Ltac scan_pct n i l A := run_to 0x5350c; let q := eval vm_compute in (A + Z.of_nat (i + n)) in eapply (pc_scan n i l A q); [ scan_side A .. | ].
Ltac scan_nul n i l A := run_to 0x5350c; let q := eval vm_compute in (A + Z.of_nat (i + n)) in eapply (pc_scan_nul n i l A q); [ scan_side A .. | ].

Tactic Notation "pose_str" ident(nm) constr(A) constr(l) constr(MI) := pose proof (ro_str _ A l MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as nm; cbn [map] in nm.
Ltac pose_rodata MI :=
pose_str RS1 0x1d915 [100; 105; 111; 117; 120; 88; 110; 0] MI;
pose_str RS2 0x16c7d [97; 65; 101; 69; 102; 70; 103; 71; 0] MI;
pose_str RS3 0x15b57 [39; 45; 43; 32; 35; 48; 0] MI;
pose_str RS4 0x1c640 [106; 122; 116; 76; 113; 0] MI;
pose_str RS5 0x146d7 [99; 67; 115; 83; 0] MI;
pose_str RS6 0x1abb9 [67; 83; 0] MI;
pose_str RS7 0x1086e [99; 115; 91; 0] MI;
pose_str RS8 0x13f97 [115; 83; 0] MI;
pose proof (ro_img8 _ 0x10460 0xaaaaaaaaaaaaaaaa MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RK.

Ltac stop_pc pc := lazymatch pc with 479088%Z => idtac | 479268%Z => idtac | 479428%Z => idtac | 358144%Z => idtac | 414124%Z => idtac end.

Ltac run := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [stop_pc pc; fail 1 | bstep] end).

Ltac fixret := try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).

Ltac call_strchr A lst :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MIc : mem_inv asegs mc |- _ =>
eapply evt_cut;
[ eapply istrchr_spec with (l := lst) (q := A) (t := []); [ | | | reflexivity];
[ lia
| exact (proj2 (ro_str _ A (lst ++ [0]) MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))
| repeat (apply Forall_cons; [lia|]); apply Forall_nil ]
| let ms' := fresh "ms'" in let PO := fresh "PO" in
intros ms' PO; destruct PO as (? & ? & ->); cbn [strchr_res Z.eqb Pos.eqb]; lits; fixret ]
end end.

Ltac call_strlen FMT l :=
eapply evt_cut;
[ eapply istrlen_spec with (s := l) (t := []); [exact (proj2 FMT)| repeat (apply Forall_cons; [lia|]); apply Forall_nil]
| let ms' := fresh "ms'" in intros ms' <-; let n := eval vm_compute in (zlength l) in change (zlength l) with n; lits; fixret ].

Ltac call_memset DIR :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut;
[ eapply imemset40_spec; [exact DIR| reflexivity| assumption| lia]
| let ms' := fresh "ms'" in let PO := fresh "PO" in let m' := fresh "m" in
let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
intros ms' PO; destruct PO as (m' & -> & MU2 & WM2 & ? & ?DIR2); clear DIR;
transport_after_call asegs mc m' MU2 WM2; clear MU2 WM2; try clear mc; rename DIR2 into DIR; fixret ]
end.

Ltac dir_L2 DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A [C8 ?w0; C8 ?w1; C8 ?b; C8 ?e; C8 ?w4] =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A [CB 8 (le8 w0); CB 8 (le8 w1); C8 b; C8 e; CB 8 (le8 w4)])
by (eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8; repeat split; reflexivity| reflexivity]);
clear DIR; rename D into DIR
end.
Ltac dir_L1 DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A ([c0; c1; c2; c3] ++ rest ++ [])) by (rewrite app_nil_r; exact DIR);
apply rw_cells_merge in D; cbn [cells_size csize cells_bytes cbytes app Nat.add] in D;
clear DIR; rename D into DIR
end.

Ltac bvlist_eq := lazymatch goal with
| |- cons _ _ = cons _ _ => apply (f_equal2 cons); [apply bv_eq; reflexivity | bvlist_eq]
| |- nil = nil => reflexivity end.
Ltac dir_L2c DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A [C8 (Z_to_bv 64 ?w0); C8 (Z_to_bv 64 ?w1); C8 ?b; C8 ?e; C8 ?w4] =>
let l0 := eval vm_compute in (w0 mod 2^32) in let h0 := eval vm_compute in ((w0 / 2^32) mod 2^32) in
let l1 := eval vm_compute in (w1 mod 2^32) in let h1 := eval vm_compute in ((w1 / 2^32) mod 2^32) in
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A [C4 (Z_to_bv 64 l0); C4 (Z_to_bv 64 h0); C4 (Z_to_bv 64 l1); C4 (Z_to_bv 64 h1); C8 b; C8 e; CB 8 (le8 w4)])
by (eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8; repeat split; reflexivity|
lazymatch goal with |- ?g => tryif has_var g then fail 1 "dir_L2c: open cells" else (vm_compute; bvlist_eq) end]);
clear DIR; rename D into DIR
end.
Ltac dir_back DIR :=
lazymatch goal with |- rw_cells _ _ _ ?cs => eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8, ?length_take, ?length_drop; repeat split; reflexivity|
lazymatch goal with |- ?g => tryif has_var g then fail 1 "dir_back: open cells" else (vm_compute; bvlist_eq) end] end.

Lemma cbytes_mapC1 : forall l, cells_bytes (map (fun z => C1 (b8 z)) l) = zb l.
Proof. unfold zb. induction l as [|z l IH]; cbn [map cells_bytes cbytes app]; [reflexivity| now rewrite IH]. Qed.

Definition pc_setup_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z) (ms' : machine_state) : Prop :=
exists (m' : mem) (junk1 junk2 : list byte),
ms' = MS (mkR (wz 0x53508) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp s1
(wz (bv_unsigned sp + -2216)) (wz 0) (wz (bv_unsigned sp + -2176)) (wz (bv_unsigned sp + -2176)) (wz 0) a5 a6 a7
(wz 10) (wz A) (wz 0x15b57) a2 s6 (wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410) (wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m' (bv_unsigned sp + -2216) [C8 (wz 0); C8 (wz 18446744073709551615); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
/\ rw_cells asegs m' (bv_unsigned sp + -2176) [CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'.

End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFy3 QZzg Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mqc.
Import Q13u Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF QoNr.Mq0. Import QdZp Qk8e.Mq0.
Import Qu3b.Mq6.
Import QTVW.Mq8 Qu3b.Mq5 QnRU.Mqf QnRU QteI.Mqb.
Import QCNF.Mq2.
Import QMPy.Mq0. Import Qu3b.Mq4.
Import QFy3. Import QJBH.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QYyZ.Mq9 QFd5 QteI.
Import QlES.
Import QXE1. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Definition OUT_DEPTH : Z := 3264.
Definition PC_DEPTH : Z := 5184.
Definition VF_DEPTH : Z := 5552.
Definition GLOBALS_TOP {BAND : Band} : Z := band_lo.
Definition STATIC_SPLIT : Z := 0x23fa0.

Section Sink.
Context {BAND : Band}.
Context {St : Type}.
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
Forall (fun iv => GLOBALS_TOP <= fst iv) W ->
SINK m' st.

Definition sink_flags_stmt : Prop :=
forall m st, SINK m st -> exists fl : byte, rw_cells asegs m Fp [CB 1 [fl]] /\ Z.land (bv_unsigned fl) 32 = 0 /\ ISH m.

Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.

Definition sink_ish_stmt : Prop := forall m st, SINK m st -> ISH m.

Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S : Z) (bs : list Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at asegs m' S (zb bs).

Definition out_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (bs : list Z) (lo : Z) (canary : word),
SINK m st ->
bytes_at asegs m (bv_unsigned a0) (zb bs) ->
Forall (fun c => 0 <= c < 256) bs -> zlength bs < 2^31 ->
szone (bv_unsigned a0) (zlength bs) ->
a1 = Z_to_bv 64 (zlength bs) ->
a2 = Z_to_bv 64 Fp ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv asegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
(bv_unsigned a0 + zlength bs <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= Fp \/ Fp + 232 <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= B \/ B + BS <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= 2^47) ->
implM asegs (OUT bs) st
(out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) bs lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5a8c) fc None m (seg_rom asegs)).

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
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FMT_FP_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv asegs m -> frm0 fc ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
implM asegs (OUTFP y w p fl t) st
(fpcall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd7108) fc None m (seg_rom asegs)).

Definition arg_ok (m : mem) (lo sp ap : Z) (slot : word) (a : parg) : Prop :=
match a with
| PA_s s => exists slack : list byte,
bytes_at asegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
/\ 0 < bv_unsigned slot
/\ szone (bv_unsigned slot) (zlength s + 1)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= B \/ B + BS <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= ap \/ ap + 8 <= bv_unsigned slot)
/\ bv_unsigned slot + zlength s + 1 + zlength slack <= 2^47
| PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
| PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
| PA_g d => bv_unsigned slot = d
| PA_li i => -2^63 <= i < 2^63 /\ bv_unsigned slot = i mod 2^64
| PA_lu u => 0 <= u < 2^64 /\ bv_unsigned slot = u
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
/\ (0 <= r <= INT_MAX).

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
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->

(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> szone (bv_unsigned a1) (zlength fmt) -> (0 <= BS) ->
((954304 <= Fp /\ Fp + 232 <= 6575456) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
((6576024 <= B /\ B + BS <= lo) \/ (bv_unsigned a2 + 8 <= B /\ B + BS <= VA)) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
implM asegs (printf_model OUT OUTFP fmt args) st
(printf_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd60d0) fc None m (seg_rom asegs)).
End Sink.

Definition printf_core1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary.

Definition printf_core1_stmt {BAND : Band} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (fmt : list Z),
bytes_at asegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
pass1_ok fmt = true ->
a0 = Z_to_bv 64 0 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m ->
(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> szone (bv_unsigned a1) (zlength fmt) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 2^64) ->
evt asegs (printf_core1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd60d0) fc None m (seg_rom asegs)).

Definition TOPOK_none (sp : Z) : Prop := sp + 16 <= 2^47.

Definition OUT_MAX : Z := 16777216.

Section StderrSink.
Context {BAND : Band}.
Context {St : Type}.
Variable B : Z.

Definition SINK_stderr (m : mem) (bs : list Z * St) : Prop :=
let buf := fst bs in
exists (flags mode : word) (tail : list byte) (rest : list byte),
rw_cells asegs m RSTDERR (file_cells flags (B + 80) (B + zlength buf) B F_STDIO_WRITE B 80 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 32 = 0 /\ Z.land (bv_unsigned flags) 8 = 0
/\ rw_cells asegs m B [CB 80 (zb buf ++ rest)]
/\ zlength buf + zlength rest = 80
/\ B + 80 < 2^63 /\ GLOBALS_TOP + 64 <= B /\ B + 96 <= 2^47
/\ ISH m.

Definition OUT_stderr (s : list Z) : M (list Z * St) unit :=
fun bs => let '(buf, st) := bs in
if OUT_MAX <? zlength s then Qc6I.Ret Unr
else if INTERNAL_BUFSIZ - zlength buf <? zlength s
then ebind (stdio_writev 2 buf s st) (fun r => Qc6I.Ret (Ok (tt, ([], snd r))))
else Qc6I.Ret (Ok (tt, (buf ++ s, st))).
Definition OUTFP_stderr (y w p fl t : Z) : M (list Z * St) Z := fun _ => Qc6I.Ret Unr.
End StderrSink.

Section StdoutSink.
Context {BAND : Band}.
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
/\ zlength (so_buf so) <= 1024
/\ ISH m.
Definition OUTFP_stdout (y w p fl t : Z) : M St Z := fun _ => Qc6I.Ret Unr.

Definition OUT_stdout (s : list Z) : M St unit :=
if OUT_MAX <? zlength s then munr else stdout_fwritex get_so set_so s.
End StdoutSink.

Definition stderr_wfile (m : mem) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x645ca0 0 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 40 = 0.

Definition fwritex_stderr_stmt {BAND : Band} : Prop :=
forall (St : Type) (B : Z),
@out_stmt _ (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr.

Definition fwritex_stdout_stmt {BAND : Band} : Prop :=
forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
(forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
@out_stmt _ St RSTDOUT RSTDOUT_BUF 1024 (SINK_stdout get_so) TOPOK_none (OUT_stdout get_so set_so).

Definition stdio_write_flush_post {BAND : Band} {St : Type} (B : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (B, B + 80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK_stderr B m' ([], st')
/\ ssp_cells m' canary.
Definition stdio_write_flush_stmt {BAND : Band} : Prop :=
forall (St : Type) (B : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list Z) (st : St) (lo : Z) (canary : word),
SINK_stderr B m (buf, st) ->
a0 = Z_to_bv 64 RSTDERR -> a2 = Z_to_bv 64 0 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> (B + 80 <= lo \/ bv_unsigned sp <= B) ->
ssp_cells m canary -> mem_inv asegs m ->
bv_unsigned a1 <= 2^47 ->
implM asegs (stdio_writev 2 buf [] : M St unit) st
(stdio_write_flush_post B ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5094) fc None m (seg_rom asegs)).

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
F (Z_to_bv 64 0xd5a38) fc None m (seg_rom asegs)).

Definition EMIT_DEPTH : Z := 5728.
Section Emit.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition emit_printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stdout_file m' (get_so st')
/\ ssp_cells m' canary.

Definition emit_printf_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (v : Z),
(forall x so, get_so (set_so so x) = so) -> (forall x so so', set_so so' (set_so so x) = set_so so' x) ->
fwritex_stdout_stmt ->
stdout_file m (get_so st) -> ISH m ->
(-2^31 <= v < 2^31) -> (bv_unsigned a1 mod 2^32 = v mod 2^32) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_emit get_so set_so v) st
(emit_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91e28) fc None m (seg_rom asegs)).

Definition FPRINTF_DEPTH : Z := 5664.

Definition AFMT_emit_d : Z := 0x14f44.      Definition AFMT_usage : Z := 0x16263.
Definition AFMT_too_big : Z := 0x1a8f3.     Definition AFMT_cannot_open : Z := 0x1ef3c.
Definition AFMT_read_error : Z := 0x1ef51.

Definition diag_args (d : diag_msg) (m : mem) (fmtp argw : word) (lo sp : Z) : Prop :=
match d with
| DUsage s | DCannotOpen s | DReadError s =>
fmtp = Z_to_bv 64 (match d with DUsage _ => AFMT_usage | DCannotOpen _ => AFMT_cannot_open | _ => AFMT_read_error end)
/\ exists slack : list byte,
bytes_at asegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
/\ (zlength s <= OUT_MAX)
/\ (bv_unsigned argw + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned argw)
/\ (GLOBALS_TOP + 64 <= bv_unsigned argw) /\ (bv_unsigned argw + zlength s + 9 <= 2^47)
/\ (bv_unsigned argw + zlength s + 1 + zlength slack <= 2^47)
| DTooBig => fmtp = Z_to_bv 64 AFMT_too_big /\ bv_unsigned argw mod 2^32 = 67108864
| _ => False
end.

Definition fprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile m'
/\ ssp_cells m' canary
/\ st' = st.

Definition fprintf_diag_stmt : Prop :=
forall (d : diag_msg)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
fwritex_stderr_stmt -> stdio_write_flush_stmt ->
stderr_wfile m -> ISH m ->
a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_diag (St:=St) d) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4fd70) fc None m (seg_rom asegs)).
End Emit.

End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb.
Import Q0z1.
Import QlES.
Import QXE1. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Ltac addr_diff E A ::=
let k :=
lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end in
let ok := eval vm_compute in (Z.ltb k 65536) in
lazymatch ok with true => k end. Ltac mkr__addr_diff_3 E A := let k :=
lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end in
let ok := eval vm_compute in (Z.ltb k 65536) in
lazymatch ok with true => k end.

Ltac has_var c := match c with context [?x] => is_var x end.
Ltac bif := try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
tryif has_var c then idtac else
(let v := eval vm_compute in c in
lazymatch v with
| true => replace c with true by (vm_compute; reflexivity); cbv iota
| false => replace c with false by (vm_compute; reflexivity); cbv iota
end) end).

Ltac subfix := repeat match goal with |- context [Z_to_bv 64 (?x - ?k)] => is_Zlit k; let nk := eval vm_compute in (- k)%Z in replace (x - k)%Z with (x + nk)%Z by lia end.
Lemma zx8_lit : forall e, 0 <= e < 2^64 -> zx8 (Z_to_bv 64 e) = Z_to_bv 64 (e mod 256).
Proof. intros e He. unfold zx8. rewrite unsigned_lit by lia. reflexivity. Qed.

Ltac bnorm :=
repeat match goal with
| |- context [zx8 (Z_to_bv 64 ?e)] => is_Zlit e; rewrite (zx8_lit e) by lia;
let v := eval vm_compute in (e mod 256)%Z in change (e mod 256)%Z with v
| |- context [bv_unsigned (Z_to_bv 64 ?e)] => is_Zlit e;
let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 e)) in change (bv_unsigned (Z_to_bv 64 e)) with v
end.
Ltac bstep := istep; subfix; bnorm; bif.

Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstep end).

Definition pcommon_entry : Z := 0x537a4.
Definition PCOMMON_STACK : Z := 2320.

Definition S_diouxXn : Z := 0x1da50.  Definition S_float : Z := 0x16dde.  Definition S_flags : Z := 0x15cb0.
Definition S_lenmod : Z := 0x1c77b.   Definition S_cCsS : Z := 0x14816.   Definition S_CS : Z := 0x1acf4.
Definition S_csb : Z := 0x1088e.      Definition S_sS : Z := 0x140d6.     Definition K_aa : Z := 0x10480.

Lemma lor_range64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
intros a b Ha Hb. pose proof (Z.lor_nonneg a b).
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
split; [lia|]. apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 64 ltac:(lia))).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|Na]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 a 64 ltac:(lia))). lia.
- destruct (Z.eq_dec b 0) as [->|Nb]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 b 64 ltac:(lia))). lia.
Qed.
Lemma lor40_and15 : forall x, Z.land (Z.lor 40 x) 15 <> 0.
Proof.
intros x E. apply (f_equal (fun z => Z.testbit z 3)) in E.
rewrite Z.land_spec, Z.lor_spec, Z.bits_0 in E. cbn in E. discriminate.
Qed.

Definition imemset_bpost (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (d n cur : Z) (k : nat) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + n)) (wz (d + n)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(cur, d + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' cur [CB k (repeat (b8 0) k)].

Lemma imemset_bloop : forall (k : nat) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (d n cur : Z) (rest : list byte),
rw_cells asegs m cur [CB k rest] -> mem_inv asegs m ->
cur + Z.of_nat k = d + n -> (0 < k)%nat -> 0 <= d -> d <= cur -> d + n < 2^64 ->
evt asegs (imemset_bpost ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d n cur k m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + n)) (wz cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75360) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until rest; intros DST MI HK K0 D0 DC DN; [lia|].
assert (LR : length rest = S k) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
pose proof (munch_refl [(cur, d + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] (S k) rest [] [1%nat; k]) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
step. change (bv_unsigned (wz 0)) with 0 in DST.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [B0 DST]. cbn [cells_size csize Nat.add Z.of_nat] in DST.
step. step.
destruct k as [|k'].
-
ifF. step. step.
apply evt_done. unfold imemset_bpost. exists m0.
replace (cur + 1) with (d + n) by lia.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
eapply rw_cells_recast'; [exact B0| cbn; split; [reflexivity| exact I]| reflexivity].
- ifT. replace (Z.pos (Pos.of_succ_nat 0)) with 1 in DST by reflexivity.
replace (Z.pos (Pos.of_succ_nat 0)) with 1 in DST by reflexivity.
eapply evt_mono; [eapply (IH ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 d n (cur + 1)); [exact DST| exact MI| lia| lia| lia| lia| lia] |].
cbv beta. intros ms' (m' & -> & MU2 & WM2 & MI2 & Z2). unfold imemset_bpost. exists m'.
split; [reflexivity|].
split. { apply (munch_trans _ m m0 m'); [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn; intros; lia. }
split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|].
assert (B0' : rw_cells asegs m' cur [C1 (b8 0)]).
{ eapply rw_cells_apart; [exact B0| exact MU2| exact WM2|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
pose proof (proj2 (rw_cells_app asegs m' cur [C1 (b8 0)] [CB (S k') (repeat (b8 0) (S k'))]) (conj B0' Z2)) as J.
eapply rw_cells_recast'; [exact J| cbn; split; [| exact I]; cbn; rewrite repeat_length; reflexivity| reflexivity].
Qed.

Definition imemset40_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (d : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + 40)) (wz (d + 40)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(d, d + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' d [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].

Lemma imemset40_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (d : Z) (cs : list cell),
rw_cells asegs m d cs -> cells_size cs = 40%nat -> mem_inv asegs m -> d + 40 < 2^64 ->
evt asegs (imemset40_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz 40) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75348) fc None m (seg_rom asegs)).
Proof.
intros until cs; intros DST SZ MI DN.
pose proof (rw_cells_bound _ _ _ _ DST) as BD. rewrite SZ in BD. cbn in BD.
pose proof (rw_cells_merge asegs m d [] cs [] ltac:(cbn [app]; rewrite app_nil_r; exact DST)) as D40.
cbn [app] in D40. rewrite SZ in D40.
assert (L15 : 0 < Z.land (Z.lor 40 d) 15 < 16).
{ pose proof (lor40_and15 d). split; [pose proof (Z.land_nonneg (Z.lor 40 d) 15); lia|].
change 16 with (2^4). replace 15 with (Z.ones 4) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
step. step. rewrite ?(unsigned_lit d) by lia. rewrite (unsigned_lit (Z.lor 40 d)) by (apply lor_range64; lia).
step. ifz. step. ifz. step. step.
eapply evt_mono; [eapply (imemset_bloop 40 ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d 40 d); [exact D40| exact MI| lia| lia| lia| lia| lia] |].
cbv beta. intros ms' (m' & -> & MU & WM & MI' & Z40). unfold imemset40_post. exists m'.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
eapply rw_cells_recast'; [exact Z40| cbn; repeat split; exact I| reflexivity].
Qed.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_nth : forall (s : list Z) (t : list byte) i, 0 <= i < zlength s ->
firstn 1 (skipn (Z.to_nat i) (zb s ++ t)) = [b8 (nth (Z.to_nat i) s 0)].
Proof.
intros s t i Hi. unfold zlength in Hi. rewrite skipn_app. unfold zb. rewrite skipn_map.
replace (Z.to_nat i - length (map (λ z : Z, b8 z) s))%nat with 0%nat by (rewrite length_map; lia). cbn [skipn].
destruct (skipn (Z.to_nat i) s) as [|c rest] eqn:E.
- exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
- cbn. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat i)), <- (nth_skipn _ s 0 0%Z), E. reflexivity.
Qed.
Lemma zb_end : forall (s : list Z) (b : byte) (t : list byte), firstn 1 (skipn (Z.to_nat (zlength s)) (zb s ++ b :: t)) = [b].
Proof.
intros s b t. unfold zlength. rewrite Nat2Z.id, skipn_app. unfold zb. rewrite skipn_all2 by (rewrite length_map; lia).
rewrite length_map, Nat.sub_diag. reflexivity.
Qed.

Section IStrlen.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (p : Z) (s : list Z) (t : list byte).
Hypothesis SRC : bytes_at asegs m p (zb s ++ b8 0 :: t).
Hypothesis BYT : Forall (fun c => 0 < c < 256) s.

Definition istrlen_post : machine_state -> Prop :=
eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (zlength s)) (wz (zlength s + 1)) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)).

Lemma istrlen_loop : forall (n : nat) (i : Z) (a2 : word), Z.of_nat n = zlength s - i -> 0 <= i <= zlength s ->
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) (wz i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x754a0) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros i a2 Hn Hi.
-
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 0]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app, ?zb_length; cbn; unfold zlength in *; lia).
replace i with (zlength s) by lia. rewrite zb_end. reflexivity. }
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS. unfold zlength in *.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
change (zxb (b8 0)) with (wz 0). step. step. bif. step. step.
apply evt_done. unfold istrlen_post, zlength. replace i with (Z.of_nat (length s)) by lia. reflexivity.
- pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
assert (CR : 0 < nth (Z.to_nat i) s 0 < 256).
{ apply (proj1 (List.Forall_forall _ _) BYT). apply nth_In. unfold zlength in *; lia. }
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 (nth (Z.to_nat i) s 0)]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app, ?zb_length; cbn; unfold zlength in *; lia).
rewrite zb_nth by lia. reflexivity. }
unfold zlength in *.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
rewrite zxb_b8, Z.mod_small by lia.
step. step. ifT. apply (IH (i + 1)); lia.
Qed.

Lemma istrlen_spec : forall (a1 a2 : word),
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x7549c) fc None m (seg_rom asegs)).
Proof.
intros a1 a2. step. apply (istrlen_loop (Z.to_nat (zlength s)) 0); unfold zlength; lia.
Qed.
End IStrlen.

Fixpoint strchr_res (q : Z) (l : list Z) (c : Z) : Z :=
match l with [] => 0 | z :: l' => if z =? c then q else strchr_res (q + 1) l' c end.

Section IStrchr.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z).
Hypothesis CR : 0 < c < 256.

Definition istrchr_post (r : Z) : machine_state -> Prop :=
fun ms' => exists a1' a3' : word,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1' (wz c) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs).

Lemma istrchr_loop : forall (l : list Z) (q : Z) (t : list byte) (a1 : word),
bytes_at asegs m q (zb l ++ b8 0 :: t) -> Forall (fun z => 0 < z < 256) l -> hd 0 l <> c ->
evt asegs (istrchr_post (strchr_res q l c))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) a1 (wz c) (wz (hd 0 l)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x7540c) fc None m (seg_rom asegs)).
Proof.
induction l as [|z l IH]; intros q t a1 STR BYT NE.
- cbn [hd strchr_res]. step. ifT. step. step. apply evt_done. unfold istrchr_post. do 2 eexists. reflexivity.
- cbn [hd] in NE |- *. apply Forall_cons_iff in BYT. destruct BYT as [Bz BYT].
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
cbn [strchr_res]. replace (z =? c) with false by (symmetry; apply Z.eqb_neq; exact NE).
step. ifF.
assert (RD : ov_read_bytes asegs m (wa (q + 1)) 1 = Some [b8 (hd 0 l)]).
{ rewrite (bytes_at_read asegs m q _ 1 1 STR) by (rewrite ?length_app, ?zb_length; cbn; lia).
destruct l as [|z' l']; reflexivity. }
assert (CR' : 0 <= hd 0 l < 256).
{ destruct l as [|z' l']; cbn; [lia|]. apply Forall_cons_iff in BYT. lia. }
step. clear RD. rewrite zxb_b8, Z.mod_small by lia. step. step. step.
destruct (Z.eq_dec (hd 0 l) c) as [E|NE'].
+ ifF. step. step. apply evt_done. unfold istrchr_post.
destruct l as [|z' l']; cbn [hd] in E; [lia|]. cbn [strchr_res]. rewrite (proj2 (Z.eqb_eq _ _) E). do 2 eexists. reflexivity.
+ ifT. apply (IH (q + 1) t); [| exact BYT| exact NE'].
pose proof STR as STR'. change (zb (z :: l) ++ b8 0 :: t) with ([b8 z] ++ (zb l ++ b8 0 :: t)) in STR'.
apply bytes_at_app in STR'. destruct STR' as [_ S2]. cbn [length Z.of_nat Pos.of_succ_nat] in S2. exact S2.
Qed.

Lemma istrchr_spec : forall (l : list Z) (q : Z) (t : list byte) (a1 a2 a3 : word),
bytes_at asegs m q (zb l ++ b8 0 :: t) -> Forall (fun z => 0 < z < 256) l -> a1 = wz c ->
evt asegs (istrchr_post (strchr_res q l c))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x753fc) fc None m (seg_rom asegs)).
Proof.
intros l q t a1 a2 a3 STR BYT ->.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
assert (RD : ov_read_bytes asegs m (wa (q + 0)) 1 = Some [b8 (hd 0 l)]).
{ rewrite (bytes_at_read asegs m q _ 0 1 STR) by (rewrite ?length_app, ?zb_length; cbn; lia). destruct l; reflexivity. }
assert (CR' : 0 <= hd 0 l < 256).
{ destruct l as [|z' l']; cbn; [lia|]. apply Forall_cons_iff in BYT. lia. }
step. clear RD. rewrite zxb_b8, Z.mod_small by lia.
step. rewrite (unsigned_lit c) by lia. change (Z.land c 255) with (Z.land c (Z.ones 8)). rewrite Z.land_ones, Z.mod_small by lia.
step. destruct (Z.eq_dec (hd 0 l) c) as [E|NE].
- ifF. step. apply evt_done. unfold istrchr_post.
destruct l as [|z' l']; cbn [hd] in E; [lia|]. cbn [strchr_res]. rewrite (proj2 (Z.eqb_eq _ _) E). do 2 eexists. reflexivity.
- ifT. apply (istrchr_loop l q t); assumption.
Qed.
End IStrchr.

Definition boxed (P : Prop) : Prop := P.

Lemma rwc_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Lemma ro_str : forall m A (l : list Z), mem_inv asegs m -> ro_bytes_b asegs A (map b8 l) = true ->
0 <= A -> A + Z.of_nat (length l) <= 2^64 -> ro_cells asegs m A (map (fun z => C1 (b8 z)) l).
Proof.
intros m A l MI RB H0 HL.
pose proof (ro_cells_image asegs m A (map b8 l) MI RB H0 ltac:(rewrite length_map; exact HL)) as R.
eapply ro_cells_recast'; [exact R| |].
- clear. induction l as [|z l IH]; cbn; [exact I|]. split; [exact I| exact IH].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. clear. induction l as [|z l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma ro_img8 : forall m A v, mem_inv asegs m -> ro_bytes_b asegs A (le8 (wz v)) = true -> 0 <= A -> A + 8 <= 2^64 ->
ro_cells asegs m A [C8 (wz v)].
Proof.
intros m A v MI RB H0 HL.
pose proof (ro_cells_image asegs m A (le8 (wz v)) MI RB H0 ltac:(rewrite length_le8; exact HL)) as R.
eapply ro_cells_recast'; [exact R| cbn; split; exact I| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
Qed.

Ltac name_towers H :=
repeat match type of H with
| context [CB ?n ?j] =>
lazymatch j with
| firstn _ _ => idtac | skipn _ _ => idtac
end;
let x := fresh "jk" in set (x := j) in H; clearbody x
end.
Ltac pc_carve ST :=
carve_frame 2240%nat ST;
lazymatch goal with FR : rw_cells _ _ _ [CB 2240 _] |- _ =>
apply (rw_cells_split_CB asegs _ _ [] 2240 _ _ [2136; 104]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
name_towers FR end.

Definition pc_prologue_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (ms' : machine_state) : Prop :=
exists (m' : mem) (jk : list byte),
ms' = MS (mkR ra (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x537e4) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -2240) [CB 2136 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma pc_prologue {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> band_lo <= lo -> lo <= bv_unsigned sp - 2320 ->
evt asegs (pc_prologue_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST MI CEIL LO.
pose proof CEIL as CEIL'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold pcommon_entry.
pc_carve ST.
do 16 bstep.
apply evt_done. unfold pc_prologue_post. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

Lemma u8_lit' : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
Lemma forallb_skipn' {X} (f : X -> bool) : forall i l, forallb f l = true -> forallb f (skipn i l) = true.
Proof. induction i as [|i IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn in H |- *. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.
Lemma cells_size_mapC1 : forall l, cells_size (map (fun c => C1 (b8 c)) l) = length l.
Proof. induction l as [|c l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma ro_C1_skipn : forall segs m A l i, ro_cells segs m A (map (fun c => C1 (b8 c)) l) -> (i <= length l)%nat ->
ro_cells segs m (A + Z.of_nat i) (map (fun c => C1 (b8 c)) (skipn i l)).
Proof.
intros segs m A l i H Hi. rewrite <- (firstn_skipn i l), map_app in H. apply ro_cells_app in H. destruct H as [_ H].
rewrite cells_size_mapC1, length_firstn, Nat.min_l in H by lia. exact H.
Qed.

Lemma pc_scan_core {BAND : Band} : forall (n : nat) (l : list Z) (p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m p (map (fun c => C1 (b8 c)) l) ->
0 <= p -> p + Z.of_nat (length l) <= 2^47 -> (n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n l) = true ->
nth n l 0 = 37 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 37) a1 a2 a3 a4 a5 a6 a7 s2 (wz (p + Z.of_nat n)) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538fc) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros l p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hp Hl Hn HB HN H37 K;
(destruct l as [|c l']; [cbn in Hn; lia|]);
change (map (fun c => C1 (b8 c)) (c :: l')) with ([C1 (b8 c)] ++ map (fun c => C1 (b8 c)) l') in FM;
apply ro_cells_app in FM; destruct FM as [C0 FM]; cbn [cells_size csize Nat.add] in FM;
cbn [forallb] in HB; apply andb_prop in HB as [Hc HB]; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2.
- cbn [nth] in H37. subst c. rewrite Z.add_0_r in K.
bstep. bstep. exact K.
- cbn [firstn forallb] in HN. apply andb_prop in HN as [Hc HN]. apply andb_prop in Hc as [Hc3 Hc4].
apply Bool.negb_true_iff, Z.eqb_neq in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc4.
bstep. bstep.
if_cases K1; zify_cond K1; rewrite ?(u8_lit' c), ?unsigned_lit in K1 by lia; [exfalso; lia|].
bstep.
if_cases K2; zify_cond K2; rewrite ?(u8_lit' c), ?unsigned_lit in K2 by lia; [exfalso; lia|].
bstep. bstep. bstep.
eapply (IH l' (p + 1)); clear IH.
+ exact FM.
+ lia.
+ cbn [length] in Hl. lia.
+ cbn [length] in Hn. lia.
+ exact HB.
+ exact HN.
+ exact H37.
+ replace (p + 1 + Z.of_nat n) with (p + Z.of_nat (S n)) by lia. exact K.
Qed.

Lemma pc_scan {BAND : Band} : forall (n i : nat) (l : list Z) (A q p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m A (map (fun c => C1 (b8 c)) l) ->
q = A + Z.of_nat (i + n) -> p = A + Z.of_nat i -> 0 <= A -> A + Z.of_nat (length l) <= 2^47 -> (i + n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n (skipn i l)) = true ->
nth (i + n) l 0 = 37 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 37) a1 a2 a3 a4 a5 a6 a7 s2 (wz q) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538fc) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m (seg_rom asegs)).
Proof.
intros n i l A q p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hq -> HA Hl Hn HB HN H37 K.
eapply (pc_scan_core n (skipn i l)).
- apply ro_C1_skipn; [exact FM| lia].
- lia.
- rewrite length_skipn. lia.
- rewrite length_skipn. lia.
- apply forallb_skipn'. exact HB.
- exact HN.
- rewrite nth_skipn. exact H37.
- replace (A + Z.of_nat i + Z.of_nat n) with q by lia. exact K.
Qed.

Lemma pc_scan_nul_core {BAND : Band} : forall (n : nat) (l : list Z) (p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m p (map (fun c => C1 (b8 c)) l) ->
0 <= p -> p + Z.of_nat (length l) <= 2^47 -> (n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n l) = true ->
nth n l 0 = 0 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 (wz (p + Z.of_nat n)) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5398c) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros l p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hp Hl Hn HB HN H0 K;
(destruct l as [|c l']; [cbn in Hn; lia|]);
change (map (fun c => C1 (b8 c)) (c :: l')) with ([C1 (b8 c)] ++ map (fun c => C1 (b8 c)) l') in FM;
apply ro_cells_app in FM; destruct FM as [C0 FM]; cbn [cells_size csize Nat.add] in FM;
cbn [forallb] in HB; apply andb_prop in HB as [Hc HB]; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2.
- cbn [nth] in H0. subst c. rewrite Z.add_0_r in K.
bstep. bstep. bstep. exact K.
- cbn [firstn forallb] in HN. apply andb_prop in HN as [Hc HN]. apply andb_prop in Hc as [Hc3 Hc4].
apply Bool.negb_true_iff, Z.eqb_neq in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc4.
bstep. bstep.
if_cases K1; zify_cond K1; rewrite ?(u8_lit' c), ?unsigned_lit in K1 by lia; [exfalso; lia|].
bstep.
if_cases K2; zify_cond K2; rewrite ?(u8_lit' c), ?unsigned_lit in K2 by lia; [exfalso; lia|].
bstep. bstep. bstep.
eapply (IH l' (p + 1)); clear IH.
+ exact FM.
+ lia.
+ cbn [length] in Hl. lia.
+ cbn [length] in Hn. lia.
+ exact HB.
+ exact HN.
+ exact H0.
+ replace (p + 1 + Z.of_nat n) with (p + Z.of_nat (S n)) by lia. exact K.
Qed.

Lemma pc_scan_nul {BAND : Band} : forall (n i : nat) (l : list Z) (A q p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m A (map (fun c => C1 (b8 c)) l) ->
q = A + Z.of_nat (i + n) -> p = A + Z.of_nat i -> 0 <= A -> A + Z.of_nat (length l) <= 2^47 -> (i + n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n (skipn i l)) = true ->
nth (i + n) l 0 = 0 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 (wz q) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5398c) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m (seg_rom asegs)).
Proof.
intros n i l A q p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hq -> HA Hl Hn HB HN H0 K.
eapply (pc_scan_nul_core n (skipn i l)).
- apply ro_C1_skipn; [exact FM| lia].
- lia.
- rewrite length_skipn. lia.
- rewrite length_skipn. lia.
- apply forallb_skipn'. exact HB.
- exact HN.
- rewrite nth_skipn. exact H0.
- replace (A + Z.of_nat i + Z.of_nat n) with q by lia. exact K.
Qed.

Ltac scan_side A := first [ lazymatch goal with H : ro_cells _ _ A _ |- ro_cells _ _ A _ => exact H end | reflexivity | lia
| apply Z.leb_le; vm_compute; reflexivity | apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity ].
Ltac scan_pct n i l A := run_to 0x538e4; let q := eval vm_compute in (A + Z.of_nat (i + n)) in eapply (pc_scan n i l A q); [ scan_side A .. | ].
Ltac scan_nul n i l A := run_to 0x538e4; let q := eval vm_compute in (A + Z.of_nat (i + n)) in eapply (pc_scan_nul n i l A q); [ scan_side A .. | ].

Tactic Notation "pose_str" ident(nm) constr(A) constr(l) constr(MI) := pose proof (ro_str _ A l MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as nm; cbn [map] in nm.
Ltac pose_rodata MI :=
pose_str RS1 0x1da50 [100; 105; 111; 117; 120; 88; 110; 0] MI;
pose_str RS2 0x16dde [97; 65; 101; 69; 102; 70; 103; 71; 0] MI;
pose_str RS3 0x15cb0 [39; 45; 43; 32; 35; 48; 0] MI;
pose_str RS4 0x1c77b [106; 122; 116; 76; 113; 0] MI;
pose_str RS5 0x14816 [99; 67; 115; 83; 0] MI;
pose_str RS6 0x1acf4 [67; 83; 0] MI;
pose_str RS7 0x1088e [99; 115; 91; 0] MI;
pose_str RS8 0x140d6 [115; 83; 0] MI;
pose proof (ro_img8 _ 0x10480 0xaaaaaaaaaaaaaaaa MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RK.

Ltac stop_pc pc := lazymatch pc with 480072%Z => idtac | 480252%Z => idtac | 480412%Z => idtac | 359128%Z => idtac | 415108%Z => idtac end.

Ltac run := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [stop_pc pc; fail 1 | bstep] end).

Ltac fixret := try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).

Ltac call_strchr A lst :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MIc : mem_inv asegs mc |- _ =>
eapply evt_cut;
[ eapply istrchr_spec with (l := lst) (q := A) (t := []); [ | | | reflexivity];
[ lia
| exact (proj2 (ro_str _ A (lst ++ [0]) MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))
| repeat (apply Forall_cons; [lia|]); apply Forall_nil ]
| let ms' := fresh "ms'" in let PO := fresh "PO" in
intros ms' PO; destruct PO as (? & ? & ->); cbn [strchr_res Z.eqb Pos.eqb]; lits; fixret ]
end end.

Ltac call_strlen FMT l :=
eapply evt_cut;
[ eapply istrlen_spec with (s := l) (t := []); [exact (proj2 FMT)| repeat (apply Forall_cons; [lia|]); apply Forall_nil]
| let ms' := fresh "ms'" in intros ms' <-; let n := eval vm_compute in (zlength l) in change (zlength l) with n; lits; fixret ].

Ltac call_memset DIR :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut;
[ eapply imemset40_spec; [exact DIR| reflexivity| assumption| lia]
| let ms' := fresh "ms'" in let PO := fresh "PO" in let m' := fresh "m" in
let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
intros ms' PO; destruct PO as (m' & -> & MU2 & WM2 & ? & ?DIR2); clear DIR;
transport_after_call asegs mc m' MU2 WM2; clear MU2 WM2; try clear mc; rename DIR2 into DIR; fixret ]
end.

Ltac dir_L2 DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A [C8 ?w0; C8 ?w1; C8 ?b; C8 ?e; C8 ?w4] =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A [CB 8 (le8 w0); CB 8 (le8 w1); C8 b; C8 e; CB 8 (le8 w4)])
by (eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8; repeat split; reflexivity| reflexivity]);
clear DIR; rename D into DIR
end.
Ltac dir_L1 DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A ([c0; c1; c2; c3] ++ rest ++ [])) by (rewrite app_nil_r; exact DIR);
apply rw_cells_merge in D; cbn [cells_size csize cells_bytes cbytes app Nat.add] in D;
clear DIR; rename D into DIR
end.

Ltac bvlist_eq := lazymatch goal with
| |- cons _ _ = cons _ _ => apply (f_equal2 cons); [apply bv_eq; reflexivity | bvlist_eq]
| |- nil = nil => reflexivity end.
Ltac dir_L2c DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A [C8 (Z_to_bv 64 ?w0); C8 (Z_to_bv 64 ?w1); C8 ?b; C8 ?e; C8 ?w4] =>
let l0 := eval vm_compute in (w0 mod 2^32) in let h0 := eval vm_compute in ((w0 / 2^32) mod 2^32) in
let l1 := eval vm_compute in (w1 mod 2^32) in let h1 := eval vm_compute in ((w1 / 2^32) mod 2^32) in
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A [C4 (Z_to_bv 64 l0); C4 (Z_to_bv 64 h0); C4 (Z_to_bv 64 l1); C4 (Z_to_bv 64 h1); C8 b; C8 e; CB 8 (le8 w4)])
by (eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8; repeat split; reflexivity|
lazymatch goal with |- ?g => tryif has_var g then fail 1 "dir_L2c: open cells" else (vm_compute; bvlist_eq) end]);
clear DIR; rename D into DIR
end.
Ltac dir_back DIR :=
lazymatch goal with |- rw_cells _ _ _ ?cs => eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8, ?length_take, ?length_drop; repeat split; reflexivity|
lazymatch goal with |- ?g => tryif has_var g then fail 1 "dir_back: open cells" else (vm_compute; bvlist_eq) end] end.

Lemma cbytes_mapC1 : forall l, cells_bytes (map (fun z => C1 (b8 z)) l) = zb l.
Proof. unfold zb. induction l as [|z l IH]; cbn [map cells_bytes cbytes app]; [reflexivity| now rewrite IH]. Qed.

Definition pc_setup_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z) (ms' : machine_state) : Prop :=
exists (m' : mem) (junk1 junk2 : list byte),
ms' = MS (mkR (wz 0x538e0) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp s1
(wz (bv_unsigned sp + -2216)) (wz 0) (wz (bv_unsigned sp + -2176)) (wz (bv_unsigned sp + -2176)) (wz 0) a5 a6 a7
(wz 10) (wz A) (wz 0x15cb0) a2 s6 (wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410) (wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m' (bv_unsigned sp + -2216) [C8 (wz 0); C8 (wz 18446744073709551615); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
/\ rw_cells asegs m' (bv_unsigned sp + -2176) [CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'.

End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXE1.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_6 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells asegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Definition sn_write_entry : Z := 0xdb794.
Definition SN_WRITE_STACK : Z := (64 + MEMCPY_ICPT_STACK)%Z.

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
/\ rw_cells asegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junk)]
/\ rw_cells asegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
/\ rw_cells asegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
/\ bytes_at asegs m' B (zb o).

Lemma sn_write_spec {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (lo : Z),
a0 = Z_to_bv 64 Fp -> a2 = Z_to_bv 64 0 ->
rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
rw_cells asegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
bytes_at asegs m B (zb o) ->
rw_cells asegs m D [CB dn junk] -> (length o < dn)%nat -> (zlength o <= n < 2^63)%Z -> (0 <= bufp < 2^64)%Z -> (B + zlength o < 2^63)%Z ->
stk asegs m lo (bv_unsigned sp) -> (band_lo <= lo)%Z -> (lo <= bv_unsigned sp - SN_WRITE_STACK)%Z -> mem_inv asegs m ->

(B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z ->
(CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z ->
(Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z ->
(D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D)%Z ->
(bv_unsigned sp <= CK)%Z -> (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
(CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z ->
(B + zlength o <= CK \/ CK + 16 <= B)%Z -> (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z ->

shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m B (zlength o) -> ((0 < zlength o)%Z -> rng_ok m D (zlength o)) ->
evt asegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D n B bufp o dn junk lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb794) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros -> -> WPOS WBASE BUF COOKIE CKC SRC DST ROOM Hn Hbufp BHI ST CEIL LO MI D1 D2 D3 D4 S1 S2 S3 S4 S5 S6 SB RC RS RD.
pose proof CEIL as CEIL'. unfold SN_WRITE_STACK, MEMCPY_ICPT_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
pose proof (bytes_at_bound _ _ _ _ SRC) as BB. pose proof (zb_length o) as LZ. rewrite LZ in BB. unfold zlength in *.
pose proof (munch_refl [(lo, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUs.
pose proof (wmono_refl asegs m) as WM.
pose_word_ranges.
carve_frame 64%nat ST.
do 15 zs.
zs. replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
zs. zs. brf K1; [exfalso; lia|]. zs. zs. zs. brf K2.
-
clear MUs.
assert (O0 : length o = 0%nat) by lia. destruct o as [|c o']; [|cbn in O0; lia]. cbn [length Z.of_nat] in *.
zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
pose proof (rw_CB_length _ _ _ _ DST) as LJ.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST.
zs. zs. zs. zs.
do 9 zs.
match goal with STa : stk asegs ?mc lo (bv_unsigned sp + -64)%Z, FRx : rw_cells asegs ?mc (bv_unsigned sp + -64)%Z _ |- _ => release_frame FRx STa (bv_unsigned sp) end.
apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
split. { cbn [zlength length Z.of_nat]. rewrite Z.add_0_r, Z.sub_0_r. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
split. { cbn [zb map app length skipn]. rewrite upd_firstn_skipn in DST by (rewrite LJ; lia). cbn [firstn app] in DST. exact DST. }
split; [assumption|]. split; [assumption|]. assumption.
-
pose proof (rw_CB_length _ _ _ _ DST) as LJ.
apply (rw_cells_split_CB asegs _ _ [] dn _ [] [length o; dn - length o]%nat) in DST; [ | cbn; lia ].
cbn [mk_CB_cells app] in DST.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb]. cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
zs. zs.

specialize (RD ltac:(lia)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SB1;
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RC1;
assert (RS1 : rng_ok mc B (Z.of_nat (length o)))
by (eapply rng_ok_munch; [exact RS| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RS)); Z.div_mod_to_equations; lia);
assert (RD1 : rng_ok mc D (Z.of_nat (length o)))
by (eapply rng_ok_munch; [exact RD| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RD)); Z.div_mod_to_equations; lia)
end.
clear MUs.
call_u (memcpy_icpt_spec D B (Z.of_nat (length o)) lo (zb o) (firstn (length o) junk));
[ exact SRC| rewrite LZ, Nat2Z.id; reflexivity| rewrite Nat2Z.id; exact DSTa| lia| assumption| lia
| unsigned_lits; eassumption| exact CEIL| unsigned_lits; unfold MEMCPY_ICPT_STACK; lia| unsigned_lits; lia| unsigned_lits; lia
| exact SB1| exact RC1| exact RS1| exact RD1|].
rewrite ?(unsigned_lit D), ?(unsigned_lit B), ?(unsigned_lit (Z.of_nat (length o))) in * by lia.
rewrite !Nat2Z.id in *.
match goal with MC : rw_cells _ _ D [CB (length o) (zb o)] |- _ => rename MC into DSTa' end.
zs. zs. zs. zs. zs. zs.
zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
pose proof (rw_CB_length _ _ _ _ DSTb) as LJb.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTb) as DA. clear DSTb.
pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 (D + Z.of_nat (length o))) DA ltac:(rewrite LJb; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length o))) with (wa (D + Z.of_nat (length o) + 0)) by (unfold wa; f_equal; lia).
pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJb; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTb. rewrite upd_length, LJb in DSTb.
zs. zs. zs. zs.
do 9 zs.
match goal with STa : stk asegs ?mc lo (bv_unsigned sp + -64)%Z, FRx : rw_cells asegs ?mc (bv_unsigned sp + -64)%Z _ |- _ => release_frame FRx STa (bv_unsigned sp) end.
apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split. { unfold zlength. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
split.
{ match goal with Ha : rw_cells _ ?mm D [CB _ ?l1], Hb : rw_cells _ ?mm (D + _)%Z [CB _ ?l2] |- _ =>
assert (J : rw_cells asegs mm D ([] ++ [CB (length o) l1; CB (dn - length o) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact Hb
| apply rw_cells_merge in J; cbn [cells_size cells_bytes csize cbytes app] in J; rewrite app_nil_r in J ] end.
replace (length o + (dn - length o + 0))%nat with dn in J by lia.
rewrite upd_firstn_skipn in J by (rewrite length_firstn, length_skipn, LJ; lia). change (Z.to_nat 0) with 0%nat in J. rewrite firstn_O, app_nil_l in J.
rewrite skipn_firstn_comm, skipn_skipn in J. replace (1 + length o)%nat with (S (length o)) in J by lia.
rewrite firstn_all2 in J by (rewrite length_skipn, LJ; lia). first [exact J | let t := type of J in idtac "J:" t; match goal with |- ?g => idtac g end; fail]. }
split; [assumption|]. split; [assumption|]. assumption.
Qed.
