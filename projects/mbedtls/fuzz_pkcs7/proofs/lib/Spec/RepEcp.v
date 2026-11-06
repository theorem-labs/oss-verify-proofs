(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RepEcp () : Init.string Init.list := ["OSSVerify.KrLib.Spec.Rep.mpi_at"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "WithSegs.pt_X"; "WithSegs.pt_Y"; "Stdlib.ZArith.BinInt.Z.add"; "WithSegs.pt_Z"; "WithSegs.mpdr_at"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "WithSegs.g_pbits"; "WithSegs.g_nbits"; "OSSVerify.KrLib.Lib.Cells.C4"; "WithSegs.g_h"; "WithSegs.g_hpad"; "WithSegs.g_modp"; "WithSegs.g_tpre"; "WithSegs.g_tpost"; "WithSegs.g_tdata"; "WithSegs.g_T"; "WithSegs.g_Tsize"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "WithSegs.g_P"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "WithSegs.grp_head_cells"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "WithSegs.g_A"; "WithSegs.g_B"; "WithSegs.g_N"; "WithSegs.ecp_point_at"; "WithSegs.g_G"; "WithSegs.grp_tail_cells"; "Stdlib.ZArith.BinInt.Z.le"; "WithSegs.g_id"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "WithSegs.mpd_freeable"; "WithSegs.grp_free_mpds"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "WithSegs.grp_kept_mpds"; "WithSegs.grp_modp_ok"; "WithSegs.mkGRP"; "WithSegs.mpd_init"; "WithSegs.pt_init"; "WithSegs.mpd_zero"; "WithSegs.pt_zero"; "WithSegs.ecp_group_at"; "WithSegs.kp_grp"; "WithSegs.kp_d"; "WithSegs.kp_Q"; "WithSegs.pt_freeable"].


Definition ECP_POINT_SIZE : Z := 48.
Definition ECP_GROUP_SIZE : Z := 192.
Definition ECP_KEYPAIR_SIZE : Z := 256.

(* [comment removed for export] *)
Definition ECP_DP_NONE : Z := 0.
Definition ECP_DP_SECP192R1 : Z := 1.  Definition ECP_DP_SECP224R1 : Z := 2.  Definition ECP_DP_SECP256R1 : Z := 3.
Definition ECP_DP_SECP384R1 : Z := 4.  Definition ECP_DP_SECP521R1 : Z := 5.
Definition ECP_DP_BP256R1 : Z := 6.     Definition ECP_DP_BP384R1 : Z := 7.     Definition ECP_DP_BP512R1 : Z := 8.
Definition ECP_DP_CURVE25519 : Z := 9.
Definition ECP_DP_SECP192K1 : Z := 10. Definition ECP_DP_SECP224K1 : Z := 11. Definition ECP_DP_SECP256K1 : Z := 12.
Definition ECP_DP_CURVE448 : Z := 13.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mpdr_at (m : mem) (LB : list blk) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepEcp ()) "(0.Vsegs,O3.O2.(1.O1.)(2.&40.(3.O1.))(4.O1.)(5.O1.)(6.O1.)(7.O1.)(8.O1.))")
(* [comment removed for export] *).

#[using="Type"] Lemma mpd_at_iff : forall m LB d, mpd_at segs m LB d <-> mpdr_at m LB d /\ (md_sg d = 1 \/ md_sg d = -1).
Proof. intros; unfold mpd_at, mpdr_at; tauto. Qed.
#[using="Type"] Lemma mpdr_of_mpd : forall m LB d, mpd_at segs m LB d -> mpdr_at m LB d.
Proof. intros m LB d [H _]; exact H. Qed.
#[using="Type"] Lemma mpd_of_mpdr : forall m LB d, mpdr_at m LB d -> (md_sg d = 1 \/ md_sg d = -1) -> mpd_at segs m LB d.
Proof. intros; split; assumption. Qed.

(* [comment removed for export] *)
Definition mpd_init (A : Z) (pad : word) : mpd := mkMPD A 1 0 0 [] pad LNull.
Definition mpd_zero (A : Z) : mpd := mkMPD A 0 0 0 [] (Z_to_bv 64 0) LNull.

(* [comment removed for export] *)
Definition mpd_freeable (d : mpd) : Prop := md_own d <> LStatic.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ecp_pt := mkPT { pt_X : mpd; pt_Y : mpd; pt_Z : mpd }.

Definition ecp_point_at (m : mem) (LB : list blk) (A : Z) (p : ecp_pt) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepEcp ()) "(9.(:.$;.(1.(<.O1.))O2.)(9.(:.$;.(1.(=.O1.))(>.O2.+10.))(9.(:.$;.(1.(?.O1.))(>.O2.+20.))(9.(10.O4.O3.(<.O1.))(9.(10.O4.O3.(=.O1.))(10.O4.O3.(?.O1.)))))))")
(* [comment removed for export] *).

Definition pt_mpds (p : ecp_pt) : list mpd := [pt_X p; pt_Y p; pt_Z p].
(* [comment removed for export] *)
Definition pt_blocks (p : ecp_pt) : list blk := flat_map mpd_blk (pt_mpds p).
Definition pt_ivs (p : ecp_pt) : list (Z * Z) := flat_map mpd_ivs (pt_mpds p).
Definition pt_freeable (p : ecp_pt) : Prop := Forall mpd_freeable (pt_mpds p).

Definition pt_init (A : Z) (px py pz : word) : ecp_pt := mkPT (mpd_init A px) (mpd_init (A + 16) py) (mpd_init (A + 32) pz).
Definition pt_zero (A : Z) : ecp_pt := mkPT (mpd_zero A) (mpd_zero (A + 16)) (mpd_zero (A + 32)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ecp_grp := mkGRP {
  g_id : Z; g_idpad : word;
  g_P : mpd; g_A : mpd; g_B : mpd; g_G : ecp_pt; g_N : mpd;
  g_pbits : Z; g_nbits : Z;
  g_h : Z; g_hpad : word;
  g_modp : Z; g_tpre : Z; g_tpost : Z; g_tdata : Z; g_T : Z; g_Tsize : Z }.

Definition grp_head_cells (g : ecp_grp) : list cell := [C4 (Z_to_bv 64 (g_id g)); C4 (g_idpad g)].
Definition grp_tail_cells (g : ecp_grp) : list cell := ltac2:(CDefT.buildp (gd_tbl_RepEcp ()) "(11.$12.(13.(2.&40.(14.O1.)))(11.$12.(13.(2.&40.(15.O1.)))(11.$12.(16.(2.&40.(17.O1.)))(11.$12.(16.(18.O1.))(11.$12.(13.(2.&40.(19.O1.)))(11.$12.(13.(2.&40.(1:.O1.)))(11.$12.(13.(2.&40.(1;.O1.)))(11.$12.(13.(2.&40.(1<.O1.)))(11.$12.(13.(2.&40.(1=.O1.)))(11.$12.(13.(2.&40.(1>.O1.)))(1?.$12.)))))))))))")
(* [comment removed for export] *).

Definition grp_mpds (g : ecp_grp) : list mpd := [g_P g; g_A g; g_B g] ++ pt_mpds (g_G g) ++ [g_N g].
Definition grp_blocks (g : ecp_grp) : list blk := flat_map mpd_blk (grp_mpds g).
(* [comment removed for export] *)
Definition grp_free_mpds (g : ecp_grp) : list mpd :=
  if g_h g =? 1 then [] else if g_h g =? 2 then [g_A g; g_B g] ++ pt_mpds (g_G g) else [g_A g; g_B g] ++ pt_mpds (g_G g) ++ [g_N g; g_P g].
(* [comment removed for export] *)
Definition grp_kept_mpds (g : ecp_grp) : list mpd :=
  if g_h g =? 1 then grp_mpds g else if g_h g =? 2 then [g_P g; g_N g] else [].

(* [comment removed for export] *)
Definition modp_ent := (Z * (Z * list word))%type.
(* [comment removed for export] *)
Definition grp_modp_ok (MT : list modp_ent) (g : ecp_grp) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepEcp ()) "(20.(:.$;.(19.O1.)=)(21.$;.Llp,$;.(21.(22.(23.&40.))Lws,(22.(23.&40.))(9.(24.(25.$;.(25.$;.(22.(23.&40.))))(26.$;.(25.$;.(22.(23.&40.)))(19.O1.)(26.$;.(22.(23.&40.))R2.R1.))O2.)(9.(:.$;.(5.(27.O1.))R2.)(9.(:.(22.(23.&40.))(6.(27.O1.))R1.)(9.(:.$28.(8.(27.O1.))$29.)(:.$;.(3.(27.O1.))+1.))))))))")
(* [comment removed for export] *).

Definition ecp_group_at (MT : list modp_ent) (m : mem) (LB : list blk) (A : Z) (g : ecp_grp) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepEcp ()) "(9.(2:.Vsegs,O4.O2.(2;.O1.))(9.(:.$;.(2<.O2.+8.)=)(9.(2=.=O2.)(9.(:.$;.(1.(27.O1.))(>.O2.+8.))(9.(:.$;.(1.(2>.O1.))(>.O2.+18.))(9.(:.$;.(1.(2?.O1.))(>.O2.+28.))(9.(:.$;.(1.(30.O1.))(>.O2.+68.))(9.(10.O4.O3.(27.O1.))(9.(10.O4.O3.(2>.O1.))(9.(10.O4.O3.(2?.O1.))(9.(31.O4.O3.(>.O2.+38.)(32.O1.))(9.(10.O4.O3.(30.O1.))(9.(2:.Vsegs,O4.(>.O2.+78.)(33.O1.))(9.(9.(34.=(35.O1.))(2=.(35.O1.)(36.+2.+1?.)))(9.(9.(34.=(14.O1.))(2=.(14.O1.)(36.+2.+40.)))(9.(9.(34.=(15.O1.))(2=.(15.O1.)(36.+2.+40.)))(9.(9.(34.=(17.O1.))(2=.(17.O1.)(36.+2.+20.)))(9.(9.(34.=(19.O1.))(2=.(19.O1.)(36.+2.+40.)))(9.(9.(34.=(1:.O1.))(2=.(1:.O1.)(36.+2.+40.)))(9.(9.(34.=(1;.O1.))(2=.(1;.O1.)(36.+2.+40.)))(9.(9.(34.=(1<.O1.))(2=.(1<.O1.)(36.+2.+40.)))(9.(9.(34.=(1=.O1.))(2=.(1=.O1.)(36.+2.+40.)))(9.(:.$;.(1>.O1.)=)(9.(37.$38.$39.(3:.O1.))(9.(37.$38.Ld,$38.(3;.(:.$28.(8.R1.)$3<.))(3=.O1.))(3>.O5.O1.))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition grp_init (A : Z) (idpad pP pA pB pX pY pZ pN hpad : word) : ecp_grp := ltac2:(CDefT.buildp (gd_tbl_RepEcp ()) "(3?.=O9.(40.(>.O:.+8.)O8.)(40.(>.O:.+18.)O7.)(40.(>.O:.+28.)O6.)(41.(>.O:.+38.)O5.O4.O3.)(40.(>.O:.+68.)O2.)===O1.======)")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition grp_zero (A : Z) : ecp_grp := ltac2:(CDefT.buildp (gd_tbl_RepEcp ()) "(3?.=(2.&40.=)(42.(>.O1.+8.))(42.(>.O1.+18.))(42.(>.O1.+28.))(43.(>.O1.+38.))(42.(>.O1.+68.))===(2.&40.=)======)")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ecp_kp := mkKP { kp_grp : ecp_grp; kp_d : mpd; kp_Q : ecp_pt }.

Definition ecp_keypair_at (MT : list modp_ent) (m : mem) (LB : list blk) (A : Z) (k : ecp_kp) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepEcp ()) "(9.(44.O5.O4.O3.O2.(45.O1.))(9.(:.$;.(1.(46.O1.))(>.O2.+<0.))(9.(10.O4.O3.(46.O1.))(9.(39.(46.O1.))(9.(31.O4.O3.(>.O2.+=0.)(47.O1.))(48.(47.O1.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition kp_blocks (k : ecp_kp) : list blk := grp_blocks (kp_grp k) ++ mpd_blk (kp_d k) ++ pt_blocks (kp_Q k).
Definition kp_mpds (k : ecp_kp) : list mpd := grp_mpds (kp_grp k) ++ kp_d k :: pt_mpds (kp_Q k).

End WithSegs.
