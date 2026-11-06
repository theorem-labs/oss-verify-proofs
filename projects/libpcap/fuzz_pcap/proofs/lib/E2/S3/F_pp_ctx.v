(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ppctx := mkPP {
  c_sp : word; c_gp : word; c_tp : word; c_ra : word; c_s0 : word; c_s1 : word; c_s2 : word;
  c_s3 : word; c_s4 : word; c_s5 : word; c_s6 : word; c_s7 : word; c_s8 : word; c_s9 : word; c_s10 : word; c_s11 : word;
  c_F : bvmap 5 word; c_fc : bv 32; c_m0 : mem;
  c_HA : Z; c_DA : Z; c_ws : word; c_wu : word; c_caplen : Z; c_len0 : Z; c_N : nat; c_lo : Z }.

Definition ppwf (c : ppctx) : Prop :=
  (0 <= c_caplen c <= Z.of_nat (c_N c))%Z
  /\ (Z.of_nat (c_N c) < 2^31)%Z
  /\ (0 <= c_len0 c < 2^32)%Z
  /\ (c_lo c <= bv_unsigned (c_sp c) - 32)%Z
  /\ (bv_unsigned (c_sp c) <= c_HA c \/ c_HA c + 24 <= bv_unsigned (c_sp c) - 32)%Z
  /\ (c_HA c + 24 <= c_DA c \/ c_DA c + Z.of_nat (c_N c) <= c_HA c)%Z
  /\ (c_DA c + Z.of_nat (c_N c) <= bv_unsigned (c_sp c) - 32)%Z
  /\ (0 <= c_DA c /\ c_DA c + Z.of_nat (c_N c) <= 2^47)%Z
  /\ (0 <= c_HA c /\ c_HA c + 24 <= 2^47)%Z
  /\ (c_HA c mod 8 = 0)%Z /\ (c_DA c mod 4 = 0)%Z.

Definition FOOT (c : ppctx) : list (Z * Z) :=
  [(bv_unsigned (c_sp c) - 32, bv_unsigned (c_sp c)); (c_HA c + 20, c_HA c + 24); (c_DA c, c_DA c + c_caplen c)]%Z.

(* [comment removed for export] *)
Definition ppinv (c : ppctx) (m : mem) (d : list Z) (hlen : Z) : Prop :=
  rw_cells ssegs m (c_HA c) [C8 (c_ws c); C8 (c_wu c); C4 (Z_to_bv 64 (c_caplen c)); C4 (Z_to_bv 64 hlen)]
  /\ bytes_at ssegs m (c_DA c) (zbytes d) /\ wr_at ssegs m (c_DA c) (Z.of_nat (length d))
  /\ Forall (fun x => 0 <= x < 256)%Z d /\ length d = c_N c
  /\ mem_inv ssegs m /\ munch (FOOT c) (c_m0 c) m /\ wmono ssegs (c_m0 c) m
  /\ stk ssegs m (c_lo c) (bv_unsigned (c_sp c) + -32)
  /\ rw_cells ssegs m (bv_unsigned (c_sp c) + -32) [C8 (c_s2 c); C8 (c_s1 c); C8 (c_s0 c); C8 (c_ra c)].

(* [comment removed for export] *)
Definition ppost (c : ppctx) (hlen : Z) (d : list Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m',
    ms' = MS (mkR (c_ra c) (c_sp c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
                  (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
             (c_F c) (ret_pc (c_ra c)) (c_fc c) None m' (seg_rom ssegs)
    /\ s0 = c_s0 c /\ s1 = c_s1 c /\ s2 = c_s2 c
    /\ munch (FOOT c) (c_m0 c) m' /\ wmono ssegs (c_m0 c) m' /\ mem_inv ssegs m'
    /\ stk ssegs m' (c_lo c) (bv_unsigned (c_sp c))
    /\ rw_cells ssegs m' (c_HA c) [C8 (c_ws c); C8 (c_wu c); C4 (Z_to_bv 64 (c_caplen c)); C4 (Z_to_bv 64 hlen)]
    /\ zarr m' (c_DA c) d.

(* [comment removed for export] *)
Notation SPM c := (Z_to_bv 64 (bv_unsigned (c_sp c) + -32)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zlia := fastfirst (first [ noevar_assumption | lia | Z.div_mod_to_equations; lia ]).
Ltac cond_fin := first [ reflexivity | apply Z.ltb_lt; zlia | apply Z.ltb_ge; zlia | apply Z.eqb_eq; zlia | apply Z.eqb_neq; zlia ].
Ltac cond_side2_alts := first [ noevar_assumption | cond_side
        | cond_side_t
        | apply lts_negZ; lia
        | rewrite ltu_swrap_swrap; cond_fin
        | rewrite eqb_swrap_swrap; cond_fin
        | rewrite ltu_swrap_small by lia; cond_fin
        | rewrite ltu_small_swrap by lia; cond_fin
        | rewrite eqb_swrap_small by lia; cond_fin
        | rewrite eqb_small_swrap by lia; cond_fin
        | apply (proj2 (Bool.negb_false_iff _)); cond_side2
        | apply (proj2 (Bool.negb_true_iff _)); cond_side2 ]
with cond_side2 :=
  rewrite ?sx32_as_swrap;
  fastfirst cond_side2_alts.
Ltac bfalse ::=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false; [cbv iota| symmetry; cond_side2] end.
Ltac btrue ::=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true; [cbv iota| symmetry; cond_side2] end.

Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- wr_at _ _ ?A _ => match goal with H : wr_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  | |- munch _ _ _ => match goal with H : munch _ _ _ |- _ => exact H end
  | |- wmono _ _ _ => match goal with H : wmono _ _ _ |- _ => exact H end
  | |- Forall _ ?d => match goal with H : Forall _ d |- _ => exact H end
  end.

(* [comment removed for export] *)
Ltac open_wf WF := destruct WF as (CAP & NB & HL0 & LO & SEP1 & SEP2 & SEP3 & DB & HB & ALH & ALD).
Ltac open_inv I :=
  destruct I as (HDR & ZB & ZW & ZR & LD & MI & MU & WM & ST & FR);
  lazymatch type of ZB with bytes_at _ _ _ (zbytes ?d) =>
    let LZ := fresh "LZ" in pose proof (zbytes_length d) as LZ; rewrite LD in LZ end;
  unfold FOOT in MU.
Ltac pp_init WF I :=
  open_wf WF; open_inv I;
  lazymatch goal with |- context [c_sp ?c] =>
    let RSP := fresh "RSP" in
    pose proof (bv_unsigned_in_range 64 (c_sp c)) as RSP; unfold bv_modulus in RSP; cbn in RSP end.

(* [comment removed for export] *)
Ltac rd1 k :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d), ZW : wr_at ssegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let H := fresh "RD" in let R := fresh "RG" in
    destruct (zarr_read1 m A d k (conj ZB (conj ZW ZR))) as [H R]; [lia|lia|];
    lstep; rewrite ?zxb_small, ?sxb_small by lia; clear H end.
Ltac rd2 k :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d), ZW : wr_at ssegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let H := fresh "RD" in let R := fresh "RG" in
    destruct (zarr_read2 m A d k (conj ZB (conj ZW ZR))) as [H R]; [lia|lia|];
    lstep; rewrite ?zx16_small by lia; clear H end.
Ltac rd4 k :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d), ZW : wr_at ssegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let H := fresh "RD" in let R := fresh "RG" in
    destruct (zarr_read4 m A d k (conj ZB (conj ZW ZR))) as [H R]; [lia|lia|];
    lstep; rewrite ?zx32_small by lia; clear H end.

(* [comment removed for export] *)
Ltac zstore_done k l :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d), ZW : wr_at ssegs ?m ?A _, ZR : Forall _ ?d, LD : length ?d = _ |- _ =>
    let ZA' := fresh "ZA" in let LD' := fresh "LD" in
    pose proof (zarr_write m A d k l (conj ZB (conj ZW ZR)) ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(repeat constructor; lia)) as ZA';
    pose proof (buf_write_at_length k l d ltac:(lia) ltac:(cbn [length]; lia)) as LD'; rewrite LD in LD';
    let lb := eval cbv beta iota delta [zbytes map] in (zbytes l) in
    change (zbytes l) with lb in ZA' |- *;
    try rewrite (Z.add_0_r A) in ZA';
    clear ZB ZW ZR; store_done;
    let LDo := fresh "LDo" in rename LD into LDo;
    destruct ZA' as (ZB & ZW & ZR); rename LD' into LD;
    let LZ := fresh "LZ" in
    lazymatch type of ZB with bytes_at _ _ _ (zbytes ?d') =>
      pose proof (zbytes_length d') as LZ; rewrite LD in LZ;
      try (lazymatch goal with H : length (zbytes d) = _ |- _ => clear H end)
    end
  end.

(* [comment removed for export] *)
Ltac name4 k :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d), ZR : Forall _ ?d |- _ =>
    let x0 := fresh "x" in let x1 := fresh "x" in let x2 := fresh "x" in let x3 := fresh "x" in let EW := fresh "EW" in
    destruct (zslice_4 k d ltac:(lia) ltac:(lia)) as (x0 & x1 & x2 & x3 & EW);
    let RW := fresh "RW" in pose proof (zslice_range k 4 d ZR) as RW; rewrite EW in RW;
    let R0 := fresh "R" in let R1 := fresh "R" in let R2 := fresh "R" in let R3 := fresh "R" in
    apply Forall_cons_iff in RW as [R0 RW]; apply Forall_cons_iff in RW as [R1 RW]; apply Forall_cons_iff in RW as [R2 RW];
    apply Forall_cons_iff in RW as [R3 RW]; clear RW
  end.
Ltac name2 k :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d), ZR : Forall _ ?d |- _ =>
    let x0 := fresh "x" in let x1 := fresh "x" in let EW := fresh "EW" in
    destruct (zslice_2 k d ltac:(lia) ltac:(lia)) as (x0 & x1 & EW);
    let RW := fresh "RW" in pose proof (zslice_range k 2 d ZR) as RW; rewrite EW in RW;
    let R0 := fresh "R" in let R1 := fresh "R" in
    apply Forall_cons_iff in RW as [R0 RW]; apply Forall_cons_iff in RW as [R1 RW]; clear RW
  end.
(* [comment removed for export] *)
Ltac drop_byte x := try (repeat match goal with H : context [x] |- _ => clear H end; clear x).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lanes_fast :=
  lazymatch goal with
  | |- (Z.lor (Z.lor ((Z.shiftl ?X 24) mod 18446744073709551616) ((Z.shiftl (Z.land ?X 65280) 8) mod 18446744073709551616))
              (Z.lor (Z.land (Z.shiftr ?X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 ?X) 24)) mod 18446744073709551616))) mod 2 ^ 32 = _ =>
      lazymatch X with bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [?a; ?b; ?c; ?d]))) =>
        exact (bswap_arith_ex1s a b c d X ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) eq_refl) end
  | |- (Z.lor (Z.lor ((Z.shiftl ?X 24) mod 18446744073709551616) (Z.land ((Z.shiftl ?X 8) mod 18446744073709551616) 16711680))
              (Z.lor (Z.land (Z.shiftr ?X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 ?X) 24)) mod 18446744073709551616))) mod 2 ^ 32 = _ =>
      lazymatch X with le_of_bytes [?a; ?b; ?c; ?d] =>
        exact (bswap_arith_ex1 a b c d X ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) eq_refl) end
  | |- (Z.shiftr (Z.lor (Z.lor ((Z.shiftl ?X0 56) mod 18446744073709551616) ((Z.shiftl (Z.land ?X0 65280) 40) mod 18446744073709551616))
         (Z.lor ((Z.shiftl (Z.land (Z.lor ((Z.shiftl ?X1 32) mod 18446744073709551616) ?X0) 16711680) 24) mod 18446744073709551616)
               ((Z.shiftl ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lor ((Z.shiftl ?X1 32) mod 18446744073709551616) ?X0)) 24)) mod 18446744073709551616) 32) mod 18446744073709551616))) 32) mod 2 ^ 32 = _ =>
      lazymatch X0 with le_of_bytes [?a; ?b; ?c; ?d] => lazymatch X1 with le_of_bytes [?e; ?f; ?g; ?h] =>
        exact (bswap_arith_ex2 a b c d e f g h X0 X1 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) eq_refl eq_refl) end end
  end.
Ltac lanes_solve :=
  unfold get_le32, get_le16;
  repeat match goal with H : zslice _ _ _ = _ |- _ => rewrite H end;
  first [ lanes_fast | bswap_arith ].
(* [comment removed for export] *)
Ltac sw_lanes k ys :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d), ZW : wr_at ssegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let SOK := fresh "SOK" in
    pose proof (zarr_store_ok m A d k 4 _ (conj ZB (conj ZW ZR)) ltac:(lia) ltac:(lia) eq_refl) as SOK;
    try rewrite Z.add_0_r in SOK;
    lstep;
    lazymatch goal with |- context [write_to_mem _ _ (le4 (Z_to_bv 64 ?E))] =>
      replace (le4 (Z_to_bv 64 E)) with (zbytes ys) by (symmetry; apply le4_of_lanes; [lanes_solve | lia | lia | lia | lia])
    end;
    zstore_done k ys
  end.
Ltac sh_lanes k ys :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d), ZW : wr_at ssegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let SOK := fresh "SOK" in
    pose proof (zarr_store_ok m A d k 2 _ (conj ZB (conj ZW ZR)) ltac:(lia) ltac:(lia) eq_refl) as SOK;
    try rewrite Z.add_0_r in SOK;
    lstep;
    lazymatch goal with |- context [write_to_mem _ _ (le2 (Z_to_bv 64 ?E))] =>
      replace (le2 (Z_to_bv 64 E)) with (zbytes ys) by (symmetry; apply le2_of_lanes; [lanes_solve | lia | lia])
    end;
    zstore_done k ys
  end.

(* [comment removed for export] *)
Ltac name_arr :=
  lazymatch goal with ZB : bytes_at ssegs _ _ (zbytes ?d') |- _ =>
    first [ is_var d'
          | let dn := fresh "d" in let Hd := fresh "Hd" in remember d' as dn eqn:Hd in * ]
  end.

(* [comment removed for export] *)
Ltac st4 k :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d) |- _ =>
    name4 k;
    lazymatch goal with EW : zslice k 4 d = [?x0; ?x1; ?x2; ?x3] |- _ =>
      sw_lanes k [x3; x2; x1; x0];
      replace [x3; x2; x1; x0] with (rev (zslice k 4 d)) in * by (rewrite EW; reflexivity);
      change (buf_write_at k (rev (zslice k 4 d)) d) with (swap_field 4 k d) in *;
      clear EW; drop_byte x0; drop_byte x1; drop_byte x2; drop_byte x3; name_arr
    end
  end.
(* [comment removed for export] *)
Ltac st2 k :=
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d) |- _ =>
    name2 k;
    lazymatch goal with EW : zslice k 2 d = [?x0; ?x1] |- _ =>
      sh_lanes k [x1; x0];
      replace [x1; x0] with (rev (zslice k 2 d)) in * by (rewrite EW; reflexivity);
      change (buf_write_at k (rev (zslice k 2 d)) d) with (swap_field 2 k d) in *;
      clear EW; drop_byte x0; drop_byte x1; name_arr
    end
  end.
(* [comment removed for export] *)
Ltac st8 k :=
  let k4 := eval cbv in (k + 4)%Z in
  lazymatch goal with ZB : bytes_at ssegs ?m ?A (zbytes ?d) |- _ =>
    name4 k; name4 k4;
    lazymatch goal with EW0 : zslice k 4 d = [?x0; ?x1; ?x2; ?x3], EW1 : zslice k4 4 d = [?x4; ?x5; ?x6; ?x7] |- _ =>
      sw_lanes k [x7; x6; x5; x4];
      sw_lanes k4 [x3; x2; x1; x0];
      replace (buf_write_at k4 [x3; x2; x1; x0] (buf_write_at k [x7; x6; x5; x4] d)) with (swap_field 8 k d) in *
        by (symmetry; apply (swap8_split k k4 d x0 x1 x2 x3 x4 x5 x6 x7); [lia | lia | reflexivity | exact EW0 | exact EW1]);
      clear EW0 EW1; drop_byte x0; drop_byte x1; drop_byte x2; drop_byte x3; drop_byte x4; drop_byte x5; drop_byte x6; drop_byte x7;
      name_arr
    end
  end.

(* [comment removed for export] *)
Ltac pp_ret :=
  lazymatch goal with FR : rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _], ST : stk _ _ _ (bv_unsigned ?spv + -32) |- _ =>
    release_frame FR ST (bv_unsigned spv) end;
  apply evt_done; unfold ppost;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo FOOT];
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [cbv delta [mkR]; reflexivity|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- zarr _ _ _ => split; [|split]; hyp_by_addr
  | |- _ => first [hyp_by_addr | assumption]
  end.

(* [comment removed for export] *)
Ltac epilog := do 5 lstep; repeat lstep; pp_ret.

(* [comment removed for export] *)
Ltac fix_u8 j :=
  match goal with Hd : ?dn = swap_field ?w ?k ?dold |- _ =>
    lazymatch goal with |- context [get_u8 dn j] =>
      let E := fresh "E" in
      assert (E : get_u8 dn j = get_u8 dold j) by (rewrite Hd; apply get_u8_swap_other; lia);
      rewrite !E; clear E
    end
  end.

Ltac fix_u8_all j :=
  repeat match goal with Hd : ?dn = swap_field ?w ?k ?dold |- context [get_u8 ?dn j] =>
      let E := fresh "E" in
      assert (E : get_u8 dn j = get_u8 dold j) by (rewrite Hd; apply get_u8_swap_other; lia);
      rewrite !E; try rewrite E in * |- ; clear E
  end.

(* [comment removed for export] *)
Ltac simpl_if := repeat match goal with
  | |- context [if true then ?a else ?b] => change (if true then a else b) with a
  | |- context [if false then ?a else ?b] => change (if false then a else b) with b end.

(* [comment removed for export] *)
Ltac run := repeat lstep; try rewrite (sx32_small (c_caplen _)) by lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac bd_side_f := symmetry; rewrite ?sx32_as_swrap; (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [cond_side2_alts]).
Ltac bd_side_x := symmetry; rewrite ?sx32_as_swrap; cond_side2_alts.
Ltac bfalse_f := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| bd_side_f] end.
Ltac btrue_f := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota| bd_side_f] end.
Ltac bfalse_x := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| bd_side_x] end.
Ltac btrue_x := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota| bd_side_x] end.
Ltac bdecide := try lstep; first [bfalse_f | btrue_f | bfalse_x | btrue_x].
(* [comment removed for export] *)
Ltac gsplit x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bdecide; cbn [orb andb negb]; epilog | bdecide; cbn [orb andb negb]].
(* [comment removed for export] *)
Ltac esplit x k :=
  let C := fresh "He" in
  destruct (Z.eqb_spec x k) as [C|C]; [bdecide; cbn [orb andb negb] | bdecide; cbn [orb andb negb]].

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ppctx := mkPP {
  c_sp : word; c_gp : word; c_tp : word; c_ra : word; c_s0 : word; c_s1 : word; c_s2 : word;
  c_s3 : word; c_s4 : word; c_s5 : word; c_s6 : word; c_s7 : word; c_s8 : word; c_s9 : word; c_s10 : word; c_s11 : word;
  c_F : bvmap 5 word; c_fc : bv 32; c_m0 : mem;
  c_HA : Z; c_DA : Z; c_ws : word; c_wu : word; c_caplen : Z; c_len0 : Z; c_N : nat; c_lo : Z; c_junk : list byte }.

Definition ppwf (c : ppctx) : Prop :=
  (0 <= c_caplen c <= Z.of_nat (c_N c))%Z
  /\ (Z.of_nat (c_N c) < 2^31)%Z
  /\ (0 <= c_len0 c < 2^32)%Z
  /\ (c_lo c <= bv_unsigned (c_sp c) - 32)%Z
  /\ (bv_unsigned (c_sp c) <= c_HA c \/ c_HA c + 24 <= bv_unsigned (c_sp c) - 32)%Z
  /\ (c_HA c + 24 <= c_DA c \/ c_DA c + Z.of_nat (c_N c) <= c_HA c)%Z
  /\ (c_DA c + Z.of_nat (c_N c) <= bv_unsigned (c_sp c) - 32)%Z
  /\ (0 <= c_DA c /\ c_DA c + Z.of_nat (c_N c) <= 2^47)%Z
  /\ (0 <= c_HA c /\ c_HA c + 24 <= 2^47)%Z
  /\ (c_HA c mod 8 = 0)%Z /\ (c_DA c mod 4 = 0)%Z /\ (0 < c_HA c)%Z /\ (0 < c_DA c)%Z.

Definition FOOT (c : ppctx) : list (Z * Z) :=
  [(bv_unsigned (c_sp c) - 32, bv_unsigned (c_sp c)); (c_HA c + 20, c_HA c + 24); (c_DA c, c_DA c + c_caplen c)]%Z.

(* [comment removed for export] *)
Definition ppinv (c : ppctx) (m : mem) (d : list Z) (hlen : Z) : Prop :=
  rw_cells usegs m (c_HA c) [C8 (c_ws c); C8 (c_wu c); C4 (Z_to_bv 64 (c_caplen c)); C4 (Z_to_bv 64 hlen)]
  /\ bytes_at usegs m (c_DA c) (zbytes d) /\ wr_at usegs m (c_DA c) (Z.of_nat (length d))
  /\ Forall (fun x => 0 <= x < 256)%Z d /\ length d = c_N c
  /\ mem_inv usegs m /\ munch (FOOT c) (c_m0 c) m /\ wmono usegs (c_m0 c) m
  /\ stk usegs m (c_lo c) (bv_unsigned (c_sp c) + -32)
  /\ rw_cells usegs m (bv_unsigned (c_sp c) + -32) [CB 8 (c_junk c); C8 (c_s1 c); C8 (c_s0 c); C8 (c_ra c)].

(* [comment removed for export] *)
Definition ppost (c : ppctx) (hlen : Z) (d : list Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m',
    ms' = MS (mkR (c_ra c) (c_sp c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
                  (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
             (c_F c) (ret_pc (c_ra c)) (c_fc c) None m' (seg_rom usegs)
    /\ s0 = c_s0 c /\ s1 = c_s1 c /\ s2 = c_s2 c
    /\ munch (FOOT c) (c_m0 c) m' /\ wmono usegs (c_m0 c) m' /\ mem_inv usegs m'
    /\ stk usegs m' (c_lo c) (bv_unsigned (c_sp c))
    /\ rw_cells usegs m' (c_HA c) [C8 (c_ws c); C8 (c_wu c); C4 (Z_to_bv 64 (c_caplen c)); C4 (Z_to_bv 64 hlen)]
    /\ zarr m' (c_DA c) d.

(* [comment removed for export] *)
Notation SPM c := (Z_to_bv 64 (bv_unsigned (c_sp c) + -32)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zlia := fastfirst (first [ noevar_assumption | lia | Z.div_mod_to_equations; lia ]).
Ltac cond_fin := first [ reflexivity | apply Z.ltb_lt; zlia | apply Z.ltb_ge; zlia | apply Z.eqb_eq; zlia | apply Z.eqb_neq; zlia ].
Ltac cond_side2_alts := first [ noevar_assumption | cond_side
        | cond_side_t
        | apply lts_negZ; lia
        | rewrite ltu_swrap_swrap; cond_fin
        | rewrite eqb_swrap_swrap; cond_fin
        | rewrite ltu_swrap_small by lia; cond_fin
        | rewrite ltu_small_swrap by lia; cond_fin
        | rewrite eqb_swrap_small by lia; cond_fin
        | rewrite eqb_small_swrap by lia; cond_fin
        | apply (proj2 (Bool.negb_false_iff _)); cond_side2
        | apply (proj2 (Bool.negb_true_iff _)); cond_side2 ]
with cond_side2 :=
  rewrite ?sx32_as_swrap;
  fastfirst cond_side2_alts.
(* [comment removed for export] *)
Lemma land_7 : forall v, (0 <= v)%Z -> Z.land v 7 = (v mod 8)%Z.
Proof. intros. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_1 : forall v, (0 <= v)%Z -> Z.land v 1 = (v mod 2)%Z.
Proof. intros. change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma ltu_neg_trueZ : forall x y, (0 <= x)%Z -> (- 2^64 < y < 0)%Z -> (x < 2^64 + y)%Z ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof.
  intros x y Hx Hy Hxy. rewrite bv_ltu_Z, (unsigned_lit x), unsigned_lit_wrap by lia.
  apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.
Lemma land1_zero : forall x, (0 <= x)%Z -> (x mod 2 = 0)%Z -> Z.land x 1 = 0%Z.
Proof. intros. rewrite land_1 by lia. assumption. Qed.
Lemma land3_zero : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 3 = 0%Z.
Proof. intros. rewrite land_3 by lia. assumption. Qed.
Lemma land7_zero : forall x, (0 <= x)%Z -> (x mod 8 = 0)%Z -> Z.land x 7 = 0%Z.
Proof. intros. rewrite land_7 by lia. assumption. Qed.
Lemma land2_zero : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 2 = 0%Z.
Proof. intros x Hx Hm. rewrite land_bit_2 by lia. rewrite Hm. reflexivity. Qed.
Lemma ltu_neg_falseZ : forall y x, (- 2^64 < y < 0)%Z -> (0 <= x)%Z -> (x <= 2^64 + y)%Z ->
  bv_ltu (Z_to_bv 64 y) (Z_to_bv 64 x) = false.
Proof.
  intros y x Hy Hx Hxy. rewrite bv_ltu_Z, (unsigned_lit x), unsigned_lit_wrap by lia.
  apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma lxor_allones : forall x, (0 <= x < 2^64)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof.
  intros x Hx.
  replace (18446744073709551615 - x)%Z with ((Z.lnot x) mod 2^64)%Z by (unfold Z.lnot; Z.div_mod_to_equations; lia).
  change 18446744073709551615%Z with (Z.ones 64).
  apply Z.bits_inj'; intros n Hn. rewrite Z.lxor_spec.
  destruct (Z_lt_le_dec n 64).
  - rewrite Z.ones_spec_low, Z.mod_pow2_bits_low, Z.lnot_spec by lia. apply Bool.xorb_true_r.
  - rewrite Z.ones_spec_high, Z.mod_pow2_bits_high by lia.
    replace x with (x mod 2^64)%Z by (apply Z.mod_small; lia). rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Ltac untrap := rewrite ?land7_zero, ?land3_zero, ?land2_zero, ?land1_zero by zlia; rewrite ?lxor_allones by lia.
Ltac cond_side2_alts ::= first [ noevar_assumption | cond_side
        | cond_side_t
        | apply lts_negZ; lia
        | apply ltu_neg_trueZ; lia
        | apply ltu_neg_falseZ; lia
        | apply eqb_trueZ; zlia | apply eqb_falseZ; zlia | apply ltu_trueZ; zlia | apply ltu_falseZ; zlia
        | rewrite ltu_swrap_swrap; cond_fin
        | rewrite eqb_swrap_swrap; cond_fin
        | rewrite ltu_swrap_small by lia; cond_fin
        | rewrite ltu_small_swrap by lia; cond_fin
        | rewrite eqb_swrap_small by lia; cond_fin
        | rewrite eqb_small_swrap by lia; cond_fin
        | apply (proj2 (Bool.negb_false_iff _)); cond_side2
        | apply (proj2 (Bool.negb_true_iff _)); cond_side2 ].
(* [comment removed for export] *)
Ltac bfalse ::=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false; [cbv iota| symmetry; cond_side2] end.
Ltac btrue ::=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true; [cbv iota| symmetry; cond_side2] end.

Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- wr_at _ _ ?A _ => match goal with H : wr_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  | |- munch _ _ _ => match goal with H : munch _ _ _ |- _ => exact H end
  | |- wmono _ _ _ => match goal with H : wmono _ _ _ |- _ => exact H end
  | |- Forall _ ?d => match goal with H : Forall _ d |- _ => exact H end
  end.

(* [comment removed for export] *)
Ltac open_wf WF := destruct WF as (CAP & NB & HL0 & LO & SEP1 & SEP2 & SEP3 & DB & HB & ALH & ALD & NZH & NZD).
Ltac open_inv I :=
  destruct I as (HDR & ZB & ZW & ZR & LD & MI & MU & WM & ST & FR);
  lazymatch type of ZB with bytes_at _ _ _ (zbytes ?d) =>
    let LZ := fresh "LZ" in pose proof (zbytes_length d) as LZ; rewrite LD in LZ end;
  unfold FOOT in MU.
Ltac pp_init WF I :=
  open_wf WF; open_inv I;
  lazymatch goal with |- context [c_sp ?c] =>
    let RSP := fresh "RSP" in
    pose proof (bv_unsigned_in_range 64 (c_sp c)) as RSP; unfold bv_modulus in RSP; cbn in RSP end.

(* [comment removed for export] *)
Ltac rd1 k :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d), ZW : wr_at usegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let H := fresh "RD" in let R := fresh "RG" in
    destruct (zarr_read1 m A d k (conj ZB (conj ZW ZR))) as [H R]; [lia|lia|];
    lstep; rewrite ?zxb_small, ?sxb_small by lia; clear H end.
Ltac rd2 k :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d), ZW : wr_at usegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let H := fresh "RD" in let R := fresh "RG" in
    destruct (zarr_read2 m A d k (conj ZB (conj ZW ZR))) as [H R]; [lia|lia|];
    lstep; rewrite ?zx16_small by lia; clear H end.
Ltac rd4 k :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d), ZW : wr_at usegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let H := fresh "RD" in let R := fresh "RG" in
    destruct (zarr_read4 m A d k (conj ZB (conj ZW ZR))) as [H R]; [lia|lia|];
    lstep; rewrite ?zx32_small by lia; clear H end.

(* [comment removed for export] *)
Ltac zstore_done k l :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d), ZW : wr_at usegs ?m ?A _, ZR : Forall _ ?d, LD : length ?d = _ |- _ =>
    let ZA' := fresh "ZA" in let LD' := fresh "LD" in
    pose proof (zarr_write m A d k l (conj ZB (conj ZW ZR)) ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(repeat constructor; lia)) as ZA';
    pose proof (buf_write_at_length k l d ltac:(lia) ltac:(cbn [length]; lia)) as LD'; rewrite LD in LD';
    let lb := eval cbv beta iota delta [zbytes map] in (zbytes l) in
    change (zbytes l) with lb in ZA' |- *;
    try rewrite (Z.add_0_r A) in ZA';
    clear ZB ZW ZR; store_done;
    let LDo := fresh "LDo" in rename LD into LDo;
    destruct ZA' as (ZB & ZW & ZR); rename LD' into LD;
    let LZ := fresh "LZ" in
    lazymatch type of ZB with bytes_at _ _ _ (zbytes ?d') =>
      pose proof (zbytes_length d') as LZ; rewrite LD in LZ;
      try (lazymatch goal with H : length (zbytes d) = _ |- _ => clear H end)
    end
  end.

(* [comment removed for export] *)
Ltac name4 k :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d), ZR : Forall _ ?d |- _ =>
    let x0 := fresh "x" in let x1 := fresh "x" in let x2 := fresh "x" in let x3 := fresh "x" in let EW := fresh "EW" in
    destruct (zslice_4 k d ltac:(lia) ltac:(lia)) as (x0 & x1 & x2 & x3 & EW);
    let RW := fresh "RW" in pose proof (zslice_range k 4 d ZR) as RW; rewrite EW in RW;
    let R0 := fresh "R" in let R1 := fresh "R" in let R2 := fresh "R" in let R3 := fresh "R" in
    apply Forall_cons_iff in RW as [R0 RW]; apply Forall_cons_iff in RW as [R1 RW]; apply Forall_cons_iff in RW as [R2 RW];
    apply Forall_cons_iff in RW as [R3 RW]; clear RW
  end.
Ltac name2 k :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d), ZR : Forall _ ?d |- _ =>
    let x0 := fresh "x" in let x1 := fresh "x" in let EW := fresh "EW" in
    destruct (zslice_2 k d ltac:(lia) ltac:(lia)) as (x0 & x1 & EW);
    let RW := fresh "RW" in pose proof (zslice_range k 2 d ZR) as RW; rewrite EW in RW;
    let R0 := fresh "R" in let R1 := fresh "R" in
    apply Forall_cons_iff in RW as [R0 RW]; apply Forall_cons_iff in RW as [R1 RW]; clear RW
  end.
(* [comment removed for export] *)
Ltac drop_byte x := try (repeat match goal with H : context [x] |- _ => clear H end; clear x).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lanes_fast :=
  lazymatch goal with
  | |- (Z.lor (Z.lor ((Z.shiftl ?X 24) mod 18446744073709551616) ((Z.shiftl (Z.land ?X 65280) 8) mod 18446744073709551616))
              (Z.lor (Z.land (Z.shiftr ?X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 ?X) 24)) mod 18446744073709551616))) mod 2 ^ 32 = _ =>
      lazymatch X with bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [?a; ?b; ?c; ?d]))) =>
        exact (bswap_arith_ex1s a b c d X ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) eq_refl) end
  | |- (Z.lor (Z.lor ((Z.shiftl ?X 24) mod 18446744073709551616) (Z.land ((Z.shiftl ?X 8) mod 18446744073709551616) 16711680))
              (Z.lor (Z.land (Z.shiftr ?X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 ?X) 24)) mod 18446744073709551616))) mod 2 ^ 32 = _ =>
      lazymatch X with le_of_bytes [?a; ?b; ?c; ?d] =>
        exact (bswap_arith_ex1 a b c d X ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) eq_refl) end
  | |- (Z.shiftr (Z.lor (Z.lor ((Z.shiftl ?X0 56) mod 18446744073709551616) ((Z.shiftl (Z.land ?X0 65280) 40) mod 18446744073709551616))
         (Z.lor ((Z.shiftl (Z.land (Z.lor ((Z.shiftl ?X1 32) mod 18446744073709551616) ?X0) 16711680) 24) mod 18446744073709551616)
               ((Z.shiftl ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lor ((Z.shiftl ?X1 32) mod 18446744073709551616) ?X0)) 24)) mod 18446744073709551616) 32) mod 18446744073709551616))) 32) mod 2 ^ 32 = _ =>
      lazymatch X0 with le_of_bytes [?a; ?b; ?c; ?d] => lazymatch X1 with le_of_bytes [?e; ?f; ?g; ?h] =>
        exact (bswap_arith_ex2 a b c d e f g h X0 X1 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) eq_refl eq_refl) end end
  end.
Ltac lanes_solve :=
  unfold get_le32, get_le16;
  repeat match goal with H : zslice _ _ _ = _ |- _ => rewrite H end;
  first [ lanes_fast | bswap_arith ].
(* [comment removed for export] *)
Ltac sw_lanes k ys :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d), ZW : wr_at usegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let SOK := fresh "SOK" in
    pose proof (zarr_store_ok m A d k 4 _ (conj ZB (conj ZW ZR)) ltac:(lia) ltac:(lia) eq_refl) as SOK;
    try rewrite Z.add_0_r in SOK;
    lstep;
    lazymatch goal with |- context [write_to_mem _ _ (le4 (Z_to_bv 64 ?E))] =>
      replace (le4 (Z_to_bv 64 E)) with (zbytes ys) by (symmetry; apply le4_of_lanes; [lanes_solve | lia | lia | lia | lia])
    end;
    zstore_done k ys
  end.
Ltac sh_lanes k ys :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d), ZW : wr_at usegs ?m ?A _, ZR : Forall _ ?d |- _ =>
    let SOK := fresh "SOK" in
    pose proof (zarr_store_ok m A d k 2 _ (conj ZB (conj ZW ZR)) ltac:(lia) ltac:(lia) eq_refl) as SOK;
    try rewrite Z.add_0_r in SOK;
    lstep;
    lazymatch goal with |- context [write_to_mem _ _ (le2 (Z_to_bv 64 ?E))] =>
      replace (le2 (Z_to_bv 64 E)) with (zbytes ys) by (symmetry; apply le2_of_lanes; [lanes_solve | lia | lia])
    end;
    zstore_done k ys
  end.

(* [comment removed for export] *)
Ltac name_arr :=
  lazymatch goal with ZB : bytes_at usegs _ _ (zbytes ?d') |- _ =>
    first [ is_var d'
          | let dn := fresh "d" in let Hd := fresh "Hd" in remember d' as dn eqn:Hd in * ]
  end.

(* [comment removed for export] *)
Ltac st4 k :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d) |- _ =>
    name4 k;
    lazymatch goal with EW : zslice k 4 d = [?x0; ?x1; ?x2; ?x3] |- _ =>
      sw_lanes k [x3; x2; x1; x0];
      replace [x3; x2; x1; x0] with (rev (zslice k 4 d)) in * by (rewrite EW; reflexivity);
      change (buf_write_at k (rev (zslice k 4 d)) d) with (swap_field 4 k d) in *;
      clear EW; drop_byte x0; drop_byte x1; drop_byte x2; drop_byte x3; name_arr
    end
  end.
(* [comment removed for export] *)
Ltac st2 k :=
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d) |- _ =>
    name2 k;
    lazymatch goal with EW : zslice k 2 d = [?x0; ?x1] |- _ =>
      sh_lanes k [x1; x0];
      replace [x1; x0] with (rev (zslice k 2 d)) in * by (rewrite EW; reflexivity);
      change (buf_write_at k (rev (zslice k 2 d)) d) with (swap_field 2 k d) in *;
      clear EW; drop_byte x0; drop_byte x1; name_arr
    end
  end.
(* [comment removed for export] *)
Ltac st8 k :=
  let k4 := eval cbv in (k + 4)%Z in
  lazymatch goal with ZB : bytes_at usegs ?m ?A (zbytes ?d) |- _ =>
    name4 k; name4 k4;
    lazymatch goal with EW0 : zslice k 4 d = [?x0; ?x1; ?x2; ?x3], EW1 : zslice k4 4 d = [?x4; ?x5; ?x6; ?x7] |- _ =>
      sw_lanes k [x7; x6; x5; x4];
      sw_lanes k4 [x3; x2; x1; x0];
      replace (buf_write_at k4 [x3; x2; x1; x0] (buf_write_at k [x7; x6; x5; x4] d)) with (swap_field 8 k d) in *
        by (symmetry; apply (swap8_split k k4 d x0 x1 x2 x3 x4 x5 x6 x7); [lia | lia | reflexivity | exact EW0 | exact EW1]);
      clear EW0 EW1; drop_byte x0; drop_byte x1; drop_byte x2; drop_byte x3; drop_byte x4; drop_byte x5; drop_byte x6; drop_byte x7;
      name_arr
    end
  end.

(* [comment removed for export] *)
Ltac pp_ret :=
  lazymatch goal with FR : rw_cells _ _ _ [CB 8 _; C8 _; C8 _; C8 _], ST : stk _ _ _ (bv_unsigned ?spv + -32) |- _ =>
    release_frame FR ST (bv_unsigned spv) end;
  apply evt_done; unfold ppost;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo c_junk FOOT];
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [cbv delta [mkR]; reflexivity|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- zarr _ _ _ => split; [|split]; hyp_by_addr
  | |- _ => first [hyp_by_addr | assumption]
  end.

(* [comment removed for export] *)
Ltac epilog := do 4 lstep; repeat lstep; pp_ret.

(* [comment removed for export] *)
Ltac fix_u8 j :=
  match goal with Hd : ?dn = swap_field ?w ?k ?dold |- _ =>
    lazymatch goal with |- context [get_u8 dn j] =>
      let E := fresh "E" in
      assert (E : get_u8 dn j = get_u8 dold j) by (rewrite Hd; apply get_u8_swap_other; lia);
      rewrite !E; clear E
    end
  end.

Ltac fix_u8_all j :=
  repeat match goal with Hd : ?dn = swap_field ?w ?k ?dold |- context [get_u8 ?dn j] =>
      let E := fresh "E" in
      assert (E : get_u8 dn j = get_u8 dold j) by (rewrite Hd; apply get_u8_swap_other; lia);
      rewrite !E; try rewrite E in * |- ; clear E
  end.

(* [comment removed for export] *)
Ltac simpl_if := repeat match goal with
  | |- context [if true then ?a else ?b] => change (if true then a else b) with a
  | |- context [if false then ?a else ?b] => change (if false then a else b) with b end.

(* [comment removed for export] *)
Ltac run := repeat lstep; try rewrite (sx32_small (c_caplen _)) by lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac bd_side_f := symmetry; rewrite ?sx32_as_swrap; (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [cond_side2_alts]).
Ltac bd_side_x := symmetry; rewrite ?sx32_as_swrap; cond_side2_alts.
Ltac bfalse_f := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| bd_side_f] end.
Ltac btrue_f := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota| bd_side_f] end.
Ltac bfalse_x := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| bd_side_x] end.
Ltac btrue_x := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota| bd_side_x] end.
Ltac bdecide := try lstep; try untrap; first [bfalse_f | btrue_f | bfalse_x | btrue_x].
(* [comment removed for export] *)
Ltac gsplit x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bdecide; cbn [orb andb negb]; epilog | bdecide; cbn [orb andb negb]].
(* [comment removed for export] *)
Ltac esplit x k :=
  let C := fresh "He" in
  destruct (Z.eqb_spec x k) as [C|C]; [bdecide; cbn [orb andb negb] | bdecide; cbn [orb andb negb]].
End TwB.
