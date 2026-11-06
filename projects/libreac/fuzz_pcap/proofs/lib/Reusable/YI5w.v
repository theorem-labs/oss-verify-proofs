(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI5w.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Record frame_st := mkFrame {
fr_ptr : Z;
fr_lpal : Z;
fr_img : Z;
fr_attr : Z;
fr_gen : Z;
fr_delay : Z;
fr_nlp : Z;
fr_ctidx : Z;
fr_disp : Z;
fr_tidx : Z
}.
Record cgif_st := mkCgif {
cg_frames : list (option frame_st);
cg_pal : Z;
cg_attr : Z;
cg_gen : Z;
cg_W : Z;
cg_H : Z;
cg_ngp : Z;
cg_loops : Z;
cg_raw : Z;
cg_cur : Z;
cg_ihead : Z;
rw_gct : Z;
rw_attr : Z;
rw_loops : Z;
rw_cur : Z
}.
Definition frame_ptr (o : option frame_st) : Z := match o with Some f => fr_ptr f | None => 0 end.
Definition raw_sgct (s : cgif_st) : Z := if Z.land (cg_attr s) 4 =? 0 then cg_ngp s else 0.
Definition frame_vals (f : frame_st) : list Z :=
[ fr_lpal f; fr_img f; fr_attr f; fr_gen f; fr_delay f; fr_nlp f; fr_ctidx f; fr_disp f; fr_tidx f ].
Definition pal_blocks (s : cgif_st) : list (Z * Z) :=
if Z.land (cg_attr s) 4 =? 0 then [(cg_pal s, 3 * cg_ngp s)] else [].
Definition frame_blocks (N : Z) (f : frame_st) : list (Z * Z) :=
(fr_ptr f, FRAME_SIZE) :: (fr_img f, N) ::
(if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]).
Definition frames_blocks (N : Z) (fs : list (option frame_st)) : list (Z * Z) :=
flat_map (fun o => match o with Some f => frame_blocks N f | None => [] end) fs.
Definition cgif_blocks (g : Z) (s : cgif_st) (N : Z) : list (Z * Z) :=
(g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s).
Definition blocks_fp (bl : list (Z * Z)) : list (Z * Z) := map (fun b => (fst b, fst b + snd b)) bl.
Definition frame_wf (gattr : Z) (f : frame_st) : Prop :=
(Z.land (fr_attr f) 1 = 0 -> Z.land gattr 4 = 0)
/\ (fr_disp f = 4 \/ fr_disp f = 8).
Definition cgif_wf (s : cgif_st) (N : Z) : Prop :=
length (cg_frames s) = 3%nat /\
1 <= cg_W s /\ 1 <= cg_H s /\ N = cg_W s * cg_H s /\ N <= 100000000 /\
(Z.land (cg_attr s) 4 = 0 -> cg_ngp s <= 256) /\
(cg_ihead s = 1 \/ (cg_ihead s = 2 /\ nth 1 (cg_frames s) None <> None)) /\
(forall f, In (Some f) (cg_frames s) -> frame_wf (cg_attr s) f).
End c.
