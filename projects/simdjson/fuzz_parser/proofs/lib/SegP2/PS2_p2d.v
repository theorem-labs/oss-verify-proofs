(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry PS2_t0 PS2_entry PS2_t0d P2D_sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require P2D_defs P2D_cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SG := P2D_defs.SG.

(* [comment removed for export] *)
Lemma D1_regs_list : map (fun k => sr_get P2D_defs.D1_regs (Z_to_bv 5 k)) rkeys =
  [EVar 29; EAlu ALU_ADD (EVar 1) (ELit (-368)); EVar 2; EVar 3; EVar 30; EVar 31; EVar 32; EVar 16; EVar 28;
   EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45;
   EVar 46; EVar 47; EVar 48; EVar 49; EVar 50; EVar 51; EVar 52; EVar 53; EVar 54].
Proof. vm_compute. reflexivity. Qed.
Lemma D2_regs_list : map (fun k => sr_get P2D_defs.D2_regs (Z_to_bv 5 k)) rkeys =
  [EVar 30; EAlu ALU_ADD (EVar 1) (ELit (-368)); EVar 2; EVar 3; EVar 31; EVar 32; EVar 33; EVar 16; EVar 28;
   EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45; EVar 46;
   EVar 47; EVar 48; EVar 49; EVar 50; EVar 51; EVar 52; EVar 53; EVar 54; EVar 55].
Proof. vm_compute. reflexivity. Qed.
Lemma D3_regs_list : map (fun k => sr_get P2D_defs.D3_regs (Z_to_bv 5 k)) rkeys =
  [EVar 30; EAlu ALU_ADD (EVar 1) (ELit (-368)); EVar 2; EVar 3; EVar 31; EVar 32; EVar 33; EVar 16; EVar 28;
   EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45; EVar 46;
   EVar 47; EVar 48; EVar 49; EVar 50; EVar 51; EVar 52; EVar 53; EVar 54; EVar 55].
Proof. vm_compute. reflexivity. Qed.

Ltac regs_tac L :=
  apply regs_ok_mkR;
  rewrite <- (map_map _ (edenot _)), L; cbn [map];
  repeat f_equal;
    first [ (cbn [edenot ev mkEZ nth ZLD1 ZLD2 app]; apply Z_to_bv_bv_unsigned)
          | (cbn [edenot ev mkEZ nth ZLD1 ZLD2 app]; reflexivity)
          | (rewrite zden_ok by reflexivity; cbn [zden nth ZLD1 ZLD2 app]; apply Z_to_bv_congr; f_equal; lia) ].

Lemma p2d_run1 : forall (zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (gpw tpw : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  let ZL := ZLD1 zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB
              (u x9)
              [u x1; u x5; u x6; u x7; u x10; u x11; u x12; u x13; u x14; u x15; u x16; u x17; u x18; u x19; u x20; u x21;
               u x22; u x23; u x24; u x25; u x26; u x27; u x28; u x29; u x30; u x31] in
  zgp = u gpw -> ztp = u tpw -> 368 <= zsp < M64 -> 0 <= THIS < M64 ->
  know_ok psegs (mkEZ ZL) m P2D_defs.D1_kn -> mem_inv psegs m -> frm0 fc ->
  ExecF.evtF SG (SX.fp_of (SP.p_A P2D_defs.P2D) (mkEZ ZL)) (SLib.xpost SG GP0 P2D_defs.P2D (mkEZ ZL) m (seg_rom psegs))
    (MS (mkR x1 (Z_to_bv 64 (zsp - 368)) gpw tpw x5 x6 x7 (Z_to_bv 64 THIS) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x294ec) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ZL Hgp Htp Hsp HTH HK HMI HZ.
  pose proof (u_rng' gpw) as Rgp. pose proof (u_rng' tpw) as Rtp.
  assert (EGP : gpw = Z_to_bv 64 zgp) by (subst zgp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (ETP : tpw = Z_to_bv 64 ztp) by (subst ztp; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite EGP, ETP.
  apply (SLib.prog_evt SG GP0 (fun _ _ => []) (fun _ => false) GP0_frame GP0_vc P2D_defs.P2D P2D_defs.P2D_IT 4000 false []
           P2D_defs.D1 P2D_cert.p2d_cert (SP.itab_ranges_sound SG _) ltac:(intros TA []) ltac:(intros Sm [])
           ltac:(left; reflexivity)).
  - exact I.
  - apply rfull_mkR.
  - regs_tac D1_regs_list.
  - exact HK.
  - constructor.
  - exact HMI.
  - exact HZ.
Qed.

Lemma p2d_run23 : forall (T : ST.tmpl) (zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB TW
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (gpw tpw : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  T = P2D_defs.D2 \/ T = P2D_defs.D3 ->
  let ZL := ZLD2 zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB
              (u x9) TW
              [u x1; u x5; u x6; u x7; u x10; u x11; u x12; u x13; u x14; u x15; u x16; u x17; u x18; u x19; u x20; u x21;
               u x22; u x23; u x24; u x25; u x26; u x27; u x28; u x29; u x30; u x31] in
  zgp = u gpw -> ztp = u tpw -> 368 <= zsp < M64 -> 0 <= THIS < M64 ->
  know_ok psegs (mkEZ ZL) m (ST.t_know T) -> mem_inv psegs m -> frm0 fc ->
  ExecF.evtF SG (SX.fp_of (SP.p_A P2D_defs.P2D) (mkEZ ZL)) (SLib.xpost SG GP0 P2D_defs.P2D (mkEZ ZL) m (seg_rom psegs))
    (MS (mkR x1 (Z_to_bv 64 (zsp - 368)) gpw tpw x5 x6 x7 (Z_to_bv 64 THIS) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (ST.t_pc T)) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HT ZL Hgp Htp Hsp HTH HK HMI HZ.
  pose proof (u_rng' gpw) as Rgp. pose proof (u_rng' tpw) as Rtp.
  assert (EGP : gpw = Z_to_bv 64 zgp) by (subst zgp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (ETP : tpw = Z_to_bv 64 ztp) by (subst ztp; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite EGP, ETP.
  apply (SLib.prog_evt SG GP0 (fun _ _ => []) (fun _ => false) GP0_frame GP0_vc P2D_defs.P2D P2D_defs.P2D_IT 4000 false []
           T P2D_cert.p2d_cert (SP.itab_ranges_sound SG _) ltac:(intros TA []) ltac:(intros Sm [])
           ltac:(destruct HT as [->| ->]; [right; left; reflexivity | right; right; left; reflexivity])).
  - exact I.
  - apply rfull_mkR.
  - destruct HT as [->| ->]; [regs_tac D2_regs_list | regs_tac D3_regs_list].
  - exact HK.
  - destruct HT as [->| ->]; constructor.
  - exact HMI.
  - exact HZ.
Qed.

(* [comment removed for export] *)
Lemma p2d_munch : forall (ZL : list Z) (zsp THIS TBASE CAPT : Z) (m m' : word -> option byte),
  nth 1 ZL 0 = zsp -> nth 16 ZL 0 = THIS -> nth 22 ZL 0 = TBASE -> nth 23 ZL 0 = CAPT ->
  (forall x : word, SP.outside_wins (mkEZ ZL) (SP.p_W P2D_defs.P2D) (u x) -> m' x = m x) ->
  368 <= zsp < M64 -> 0 <= THIS -> THIS + 28 < M64 -> 0 <= TBASE -> 0 <= CAPT -> TBASE + 8 * CAPT < M64 ->
  munch [(zsp - 368, zsp); (THIS + 24, THIS + 28); (TBASE, TBASE + 8 * CAPT)] m m'.
Proof.
  intros ZL zsp THIS TBASE CAPT m m' N1 N16 N22 N23 FR. intros. intros x Hx. apply FR. unfold SP.outside_wins. cbn [SP.p_W P2D_defs.P2D].
  pose proof (u_rng' x).
  cbn [outside] in Hx.
  repeat constructor; cbn [SP.win_den]; rewrite ?u_zden by reflexivity;
    cbn [zden P2D_defs.vSP P2D_defs.vTHIS P2D_defs.vTBASE P2D_defs.vCAPT P2D_defs.V P2D_defs.mul];
    rewrite ?N1, ?N16, ?N22, ?N23; rewrite ?(Z.mod_small _ M64) by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma p2d_xret_regs : forall (ZL : list Z) (E' : env) (R' : bvmap 5 word),
  SP.gagree 28 (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' -> rfull R' -> regs_ok E' (ST.t_regs P2D_defs.XRET) R' ->
  exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    R' = mkR (Z_to_bv 64 (nth 0 ZL 0)) (Z_to_bv 64 (nth 1 ZL 0)) (Z_to_bv 64 (nth 2 ZL 0)) (Z_to_bv 64 (nth 3 ZL 0)) x5 x6 x7
             (Z_to_bv 64 (nth 4 ZL 0)) (Z_to_bv 64 (nth 5 ZL 0)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (nth 6 ZL 0)) (Z_to_bv 64 (nth 7 ZL 0)) (Z_to_bv 64 (nth 8 ZL 0)) (Z_to_bv 64 (nth 9 ZL 0))
             (Z_to_bv 64 (nth 10 ZL 0)) (Z_to_bv 64 (nth 11 ZL 0)) (Z_to_bv 64 (nth 12 ZL 0)) (Z_to_bv 64 (nth 13 ZL 0))
             (Z_to_bv 64 (nth 14 ZL 0)) (Z_to_bv 64 (nth 15 ZL 0)) x28 x29 x30 x31.
Proof.
  intros ZL E' R' Hg Hb HF HR.
  rewrite (regs_ok_canon E' _ R' HF HR).
  assert (EV : forall k, (k < 28)%nat -> edenot E' (EVar k) = Z_to_bv 64 (nth k ZL 0)).
  { intros k Hk. rewrite <- (SP.edenot_gagree 28 _ _ (EVar k) Hg Hb ltac:(cbn; apply Nat.leb_le; lia)). reflexivity. }
  change (sr_get (ST.t_regs P2D_defs.XRET) 1) with (EVar 0); change (sr_get (ST.t_regs P2D_defs.XRET) 2) with (EVar 1);
  change (sr_get (ST.t_regs P2D_defs.XRET) 3) with (EVar 2); change (sr_get (ST.t_regs P2D_defs.XRET) 4) with (EVar 3);
  change (sr_get (ST.t_regs P2D_defs.XRET) 8) with (EVar 4); change (sr_get (ST.t_regs P2D_defs.XRET) 9) with (EVar 5);
  change (sr_get (ST.t_regs P2D_defs.XRET) 18) with (EVar 6); change (sr_get (ST.t_regs P2D_defs.XRET) 19) with (EVar 7);
  change (sr_get (ST.t_regs P2D_defs.XRET) 20) with (EVar 8); change (sr_get (ST.t_regs P2D_defs.XRET) 21) with (EVar 9);
  change (sr_get (ST.t_regs P2D_defs.XRET) 22) with (EVar 10); change (sr_get (ST.t_regs P2D_defs.XRET) 23) with (EVar 11);
  change (sr_get (ST.t_regs P2D_defs.XRET) 24) with (EVar 12); change (sr_get (ST.t_regs P2D_defs.XRET) 25) with (EVar 13);
  change (sr_get (ST.t_regs P2D_defs.XRET) 26) with (EVar 14); change (sr_get (ST.t_regs P2D_defs.XRET) 27) with (EVar 15).
  rewrite !EV by lia. do 15 eexists. reflexivity.
Qed.
