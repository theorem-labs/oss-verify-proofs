(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill SymAux DSLayout FillWinMem TreeMem BitsLib RomRead STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface DeflateState Trees TreeModel Deflate DeflInitLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import DInit6_M.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u Callee6u TreesRod6u TreesApi6u TrApi6u TrSmall6u.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition A6_TR_INIT : Z := 0x1b6d0.
Definition A6_RA_TI : Z := 0x16f24.
Definition A6_RA_RK : Z := 0x16890.
Definition A6_RA_MS : Z := 0x1692c.
Definition A6_ZCALLOC : Z := 0x1a9f4.
Definition A6_ZCFREE : Z := 0x1aa04.
Definition A6_DATALEN : Z := 0x3d6a0.

Definition I0 (h wnd prv hd : Z) : simg :=
  [(0, 8%nat, h + 8); (8, 4%nat, 42); (48, 4%nat, 1); (56, 8%nat, 0); (80, 4%nat, 32768); (84, 4%nat, 15);
   (88, 4%nat, 32767); (96, 8%nat, wnd); (112, 8%nat, prv); (120, 8%nat, hd); (132, 4%nat, 32768);
   (136, 4%nat, 15); (140, 4%nat, 32767); (144, 4%nat, 5); (5896, 4%nat, 16384); (5952, 8%nat, 0)].   (* 1.4: high_water at 5952 *)

Lemma ret_ok_zw : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_ok (zw z).
Proof. intros z Hz H2. apply ret_ok_even. rewrite u_zw_small by lia. exact H2. Qed.

Lemma cell_write_same_at : forall M a b (w : nat) v,
  b = a -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell s6u_segs (wbytes M (zw b) (Z_to_le_bytes w v)) a w v.
Proof. intros M a b w v -> Ha Hw. apply cell_write_same; assumption. Qed.


Lemma mod16_mod8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
  intros x H. apply (proj1 (Z.mod_divide x 16 ltac:(lia))) in H. destruct H as [q ->].
  replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma mod16_p8_mod8 : forall x, x mod 16 = 0 -> (x + 8) mod 8 = 0.
Proof.
  intros x H. apply (proj1 (Z.mod_divide x 16 ltac:(lia))) in H. destruct H as [q ->].
  replace (q * 16 + 8) with ((q * 2 + 1) * 8) by lia. apply Z.mod_mul. lia.
Qed.


Lemma rom_cell : forall m a (w : nat) v,
  rom_clear m 0x10000 0x2c3f8 -> 0x10000 <= a -> a + Z.of_nat w <= 0x2c3f8 ->
  rdn s6u_segs (fun _ : word => @None byte) (zw a) w = Some (Z_to_le_bytes w v) ->
  cell s6u_segs m a w v.
Proof.
  intros m a w v HR Ha Hw E. unfold cell. rewrite <- E.
  apply rdn_ext; rewrite u_zw_small by lia; [lia|]. intros x Hx. apply HR. lia.
Qed.

Lemma wbytes_app_zw : forall bs1 bs2 m z,
  wbytes m (zw z) (bs1 ++ bs2) = wbytes (wbytes m (zw z) bs1) (zw (z + Z.of_nat (length bs1))) bs2.
Proof.
  induction bs1 as [|b bs1 IH]; intros bs2 m z.
  - cbn [app wbytes length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - cbn [app wbytes length]. unfold zw at 1 3. rewrite Z2bv_add1. fold (zw (z + 1)).
    rewrite IH. f_equal. f_equal. lia.
Qed.

Lemma wsplit8 : forall m a,
  wbytes m (zw a) (Z_to_le_bytes 8 0) = wbytes (wbytes m (zw a) (Z_to_le_bytes 4 0)) (zw (a + 4)) (Z_to_le_bytes 4 0).
Proof.
  intros m a. change (Z_to_le_bytes 8 0) with (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 0).
  rewrite wbytes_app_zw. reflexivity.
Qed.

Lemma cells2_zero : forall m P N,
  cells s6u_segs m P 1 1 (2 * N) (fun _ => 0) -> 0 <= P -> P + 2 * N < 2 ^ 64 ->
  cells s6u_segs m P 2 2 N (fun _ => 0).
Proof.
  intros m P N Hc HP HPN i Hi. unfold cell.
  rewrite (cells_rdn_bytes s6u_segs m P (2 * N) (fun _ => 0) (2 * i) 2 Hc) by lia. reflexivity.
Qed.
Lemma mod16_p65534_mod2 : forall x, x mod 16 = 0 -> (x + 65534) mod 2 = 0.
Proof.
  intros x H. apply (proj1 (Z.mod_divide x 16 ltac:(lia))) in H. destruct H as [q ->].
  replace (q * 16 + 65534) with ((q * 8 + 32767) * 2) by lia. apply Z.mod_mul. lia.
Qed.

Section INIT.
Variables (mem : word -> option byte) (h s wnd prv hd pb cb cp n : Z) (sv20 sv21 sv22 sv23 : word) (raDI : Z).
Variable regs0 : bvmap 5 word.

Variable ZCEIL : Z.
Hypothesis Hh : (0x5f000 <= ZCEIL /\ ZCEIL + 1024 <= h) /\ h + 120 <= 2 ^ 47.
Hypothesis Hh16 : h mod 16 = 0.
Hypothesis HS16 : s mod 16 = 0.
Hypothesis HHD16 : hd mod 16 = 0.
Hypothesis HS : 0 < s /\ s + 5968 <= ZCEIL.
Hypothesis HW : 0 < wnd /\ wnd + 65536 <= ZCEIL.
Hypothesis HP : 0 < prv /\ prv + 65536 <= ZCEIL.
Hypothesis HHD : 0 < hd /\ hd + 65536 <= ZCEIL.
Hypothesis HB : 0 < pb /\ pb + 65536 <= ZCEIL.
Hypothesis HSi : s + 5968 <= 0x10000 \/ 0x5f000 <= s.
Hypothesis HWi : wnd + 65536 <= 0x10000 \/ 0x5f000 <= wnd.
Hypothesis HPi : prv + 65536 <= 0x10000 \/ 0x5f000 <= prv.
Hypothesis HHi : hd + 65536 <= 0x10000 \/ 0x5f000 <= hd.
Hypothesis HBi : pb + 65536 <= 0x10000 \/ 0x5f000 <= pb.
Hypothesis Hcb : 0 <= cb < 2 ^ 63.
Hypothesis Hcp : 0 <= cp < 2 ^ 63.
Hypothesis Hn : 0 <= n < 2 ^ 63.
Hypothesis HraDI : 0 <= raDI < 2 ^ 64 /\ raDI mod 2 = 0.
Hypothesis DSW : s + 5968 <= wnd \/ wnd + 65536 <= s.
Hypothesis DSQ : s + 5968 <= prv \/ prv + 65536 <= s.
Hypothesis DSH : s + 5968 <= hd \/ hd + 65536 <= s.
Hypothesis DSB : s + 5968 <= pb \/ pb + 65536 <= s.
Hypothesis DWP : wnd + 65536 <= prv \/ prv + 65536 <= wnd.
Hypothesis DWH : wnd + 65536 <= hd \/ hd + 65536 <= wnd.
Hypothesis DWB : wnd + 65536 <= pb \/ pb + 65536 <= wnd.
Hypothesis DPH : prv + 65536 <= hd \/ hd + 65536 <= prv.
Hypothesis DPB : prv + 65536 <= pb \/ pb + 65536 <= prv.
Hypothesis DHB : hd + 65536 <= pb \/ pb + 65536 <= hd.
Hypothesis MK : mapped mem (h - 1024) (1024 + 120).
Hypothesis MS : mapped mem s 5968.
Hypothesis MW : mapped mem wnd 65536.
Hypothesis MP : mapped mem prv 65536.
Hypothesis MH : mapped mem hd 65536.
Hypothesis MB : mapped mem pb 65536.
Hypothesis HROM : forall x : word, 0x10000 <= bv_unsigned x < 0x2c3f8 -> mem x = None.
Hypothesis Cra : cell s6u_segs mem (h + -8) 8 raDI.
Hypothesis Ccb : cell s6u_segs mem (h + -16) 8 cb.
Hypothesis Ccp : cell s6u_segs mem (h + -24) 8 cp.
Hypothesis Cn : cell s6u_segs mem (h + -32) 8 n.
Hypothesis Cdl : cell s6u_segs mem (h + -40) 8 A6_DATALEN.
Hypothesis C20 : cell s6u_segs mem (h + -48) 8 (bv_unsigned sv20).
Hypothesis C21 : cell s6u_segs mem (h + -56) 8 (bv_unsigned sv21).
Hypothesis C22 : cell s6u_segs mem (h + -64) 8 (bv_unsigned sv22).
(* 1.4 UBSan: deflateInit2_'s 80-byte frame also saves s7 (x23) at 8(sp) = h - 72; the epilogue reloads it *)
Hypothesis C23 : cell s6u_segs mem (h + -72) 8 (bv_unsigned sv23).
Hypothesis Z56 : cell s6u_segs mem (h + 64) 8 s.
Hypothesis Z64 : cell s6u_segs mem (h + 72) 8 A6_ZCALLOC.
Hypothesis Z72 : cell s6u_segs mem (h + 80) 8 A6_ZCFREE.
Hypothesis Z80 : cell s6u_segs mem (h + 88) 8 0.
Hypothesis Z48 : cell s6u_segs mem (h + 56) 8 0.
Hypothesis HI0 : SIMG s6u_segs mem s 5968 (I0 h wnd prv hd).
Hypothesis ZW : cells s6u_segs mem wnd 1 1 65536 (fun _ => 0).
Hypothesis ZPV : cells s6u_segs mem prv 1 1 65536 (fun _ => 0).
Hypothesis ZHD : cells s6u_segs mem hd 1 1 65536 (fun _ => 0).
Hypothesis ZPB : cells s6u_segs mem pb 1 1 65536 (fun _ => 0).
(* 1.4 UBSan: s2 = s + 5888, s3 = strategy 0, s4 = level 6, s5 = wrap 1, s6 = memLevel 8 *)
Hypothesis P2 : getr regs0 2 = zw (h + -80).
Hypothesis P8 : getr regs0 8 = zw (h + 8).
Hypothesis P9 : getr regs0 9 = zw s.
Hypothesis P10 : getr regs0 10 = zw pb.
Hypothesis P18 : getr regs0 18 = zw (s + 5888).
Hypothesis P19 : getr regs0 19 = zw 0.
Hypothesis P20 : getr regs0 20 = zw 6.
Hypothesis P21 : getr regs0 21 = zw 1.
Hypothesis P22 : getr regs0 22 = zw 8.

Definition iC : cfg := CFG [] [] [EVar 44%nat] [0x1b6d0; 0x2ac28] [].
Definition iC2 : cfg := CFG [] [] [EVar 36%nat] [0x1b6d0; 0x2ac28] [].


(* 1.4 UBSan: deflateReset and deflateResetKeep also save s2 (= n) at h - 32 / h - 64; adler32_z's frame saves
   s7 = sv23 (deflateInit2_ reloaded it) at h - 136 and ra = 0x16e70 at h - 72; deflateResetKeep now clears s + 56 *)
Definition memA : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (zw (s + 16)) (Z_to_le_bytes 8 pb))
    (zw (s + 24)) (Z_to_le_bytes 8 65536))
    (zw (s + 196)) (Z_to_le_bytes 4 6))
    (zw (s + 200)) (Z_to_le_bytes 4 0))
    (zw (s + 5888)) (Z_to_le_bytes 8 (pb + 16384)))
    (zw (s + 5904)) (Z_to_le_bytes 4 49149))
    (zw (s + 72)) (Z_to_le_bytes 1 8))
    (zw (h + -8)) (Z_to_le_bytes 8 raDI))
    (zw (h + -16)) (Z_to_le_bytes 8 cb))
    (zw (h + -24)) (Z_to_le_bytes 8 cp))
    (zw (h + -32)) (Z_to_le_bytes 8 n))
    (zw (h + -40)) (Z_to_le_bytes 8 92304))
    (zw (h + -48)) (Z_to_le_bytes 8 (h + 8)))
    (zw (h + -56)) (Z_to_le_bytes 8 cp))
    (zw (h + -64)) (Z_to_le_bytes 8 n))
    (zw (h + 24)) (Z_to_le_bytes 8 0))
    (zw (h + 48)) (Z_to_le_bytes 8 0))
    (zw (h + 56)) (Z_to_le_bytes 8 0))
    (zw (h + 96)) (Z_to_le_bytes 4 2))
    (zw (s + 32)) (Z_to_le_bytes 8 pb))
    (zw (s + 40)) (Z_to_le_bytes 8 0))
    (zw (s + 8)) (Z_to_le_bytes 4 42))
    (zw (h + -72)) (Z_to_le_bytes 8 93904))
    (zw (h + -80)) (Z_to_le_bytes 8 s))
    (zw (h + -88)) (Z_to_le_bytes 8 (h + 8)))
    (zw (h + -96)) (Z_to_le_bytes 8 n))
    (zw (h + -104)) (Z_to_le_bytes 8 251552))
    (zw (h + -112)) (Z_to_le_bytes 8 (bv_unsigned sv20)))
    (zw (h + -120)) (Z_to_le_bytes 8 (bv_unsigned sv21)))
    (zw (h + -128)) (Z_to_le_bytes 8 (bv_unsigned sv22)))
    (zw (h + -136)) (Z_to_le_bytes 8 (bv_unsigned sv23)))
    (zw (h + -144)) (Z_to_le_bytes 8 (bv_unsigned (getr regs0 24))))
    (zw (h + -152)) (Z_to_le_bytes 8 (bv_unsigned (getr regs0 25))))
    (zw (h + -160)) (Z_to_le_bytes 8 (bv_unsigned (getr regs0 26))))
    (zw (h + -168)) (Z_to_le_bytes 8 (bv_unsigned (getr regs0 27))))
    (zw (h + 104)) (Z_to_le_bytes 8 1))
    (zw (s + 56)) (Z_to_le_bytes 8 0))
    (zw (s + 76)) (Z_to_le_bytes 4 (-2)).

Definition A_CLOB : list reg := [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma seg_A :
  exists R,
    msteps s6u_segs (mkst regs0 (0x16620 : word) mem s6u_rom) (mkst R (0x1b6d0 : word) memA s6u_rom)
    /\ getr R 1 = zw A6_RA_TI /\ getr R 10 = zw s /\ getr R 2 = zw (h + -64) /\ getr R 8 = zw s /\ getr R 9 = zw (h + 8)
    /\ getr R 18 = zw 0 (* 1.4: deflateResetKeep sets s2 = 0 (`li s2,0` at 0x16e94; level 6 skips the reload) *)
    /\ getr R 19 = zw A6_DATALEN /\ getr R 20 = sv20 /\ getr R 21 = sv21 /\ getr R 22 = sv22
    /\ getr R 23 = sv23 /\ getr R 24 = getr regs0 24 /\ getr R 25 = getr regs0 25 /\ getr R 26 = getr regs0 26 /\ getr R 27 = getr regs0 27
    /\ (forall r : reg, reg_in r A_CLOB = false -> getr R r = getr regs0 r).
Proof.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB.
  pose proof (SIMG_cell_in s6u_segs mem s 5968 _ 5896 4 16384 HI0 ltac:(cbn; tauto)) as F5896.
  pose proof (SIMG_cell_in s6u_segs mem s 5968 _ 96 8 wnd HI0 ltac:(cbn; tauto)) as F96.
  pose proof (SIMG_cell_in s6u_segs mem s 5968 _ 112 8 prv HI0 ltac:(cbn; tauto)) as F112.
  pose proof (SIMG_cell_in s6u_segs mem s 5968 _ 120 8 hd HI0 ltac:(cbn; tauto)) as F120.
  pose proof (SIMG_cell_in s6u_segs mem s 5968 _ 0 8 (h + 8) HI0 ltac:(cbn; tauto)) as Fs0.
  pose proof Fs0 as Fs0'. rewrite Z.add_0_r in Fs0'.
  pose proof (SIMG_cell_in s6u_segs mem s 5968 _ 8 4 42 HI0 ltac:(cbn; tauto)) as F8.
  pose proof (SIMG_cell_in s6u_segs mem s 5968 _ 48 4 1 HI0 ltac:(cbn; tauto)) as F48.
  unfold mapped in MK, MS. unfold A6_DATALEN, A6_ZCALLOC, A6_ZCFREE in *.
  pose proof (u64_range sv20) as U20. pose proof (u64_range sv21) as U21. pose proof (u64_range sv22) as U22.
  pose proof (u64_range (getr regs0 23)) as U23. pose proof (u64_range (getr regs0 24)) as U24. pose proof (u64_range (getr regs0 25)) as U25.
  pose proof (u64_range (getr regs0 26)) as U26. pose proof (u64_range (getr regs0 27)) as U27.
  pose proof (u64_range sv23) as U23'.
  pose proof (mod16_mod8 s HS16) as US8. pose proof (mod16_p8_mod8 h Hh16) as UH8.
  (* 1.4 path: the four pointer checks and the overflow check, deflateResetKeep's null / alignment checks, then
     `bne a2,a0` (state->strm == strm: falls through; 1.3.1 was `beq` taken), the status range test (42: taken to the
     666 / 42 compares; `beq a2,a3` 42 taken in 1.4), wrap 1, adler32_z(0, NULL, 0) (two), and level 6 != 0 (taken) *)
  symex s6u_segs iC 200%nat
    [false; false; false; false; false;  false; false; false; false; false; false; false; true; false; true; true; false; false;  true; true;  true]
    [RVal (ELit 16384); RVal (EVar 34); RVal (EVar 35); RVal (EVar 36);
     RVal (EVar 44); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (ELit 0x3d6a0); RVal (EVar 41); RVal (EVar 42); RVal (EVar 43);
     RVal (EVar 45);
     RVal (ELit 0x1a9f4); RVal (ELit 0x1aa04); RVal (EVar 33); RVal (EAdd (EVar 32) (ELit 8)); RVal (ELit 42); RVal (ELit 1)]
    [(2, EAdd (EVar 32) (ELit (-80))); (8, EAdd (EVar 32) (ELit 8)); (9, EVar 33); (10, EVar 37); (18, EAdd (EVar 33) (ELit 5888));
     (19, ELit 0); (20, ELit 6); (21, ELit 1); (22, ELit 8)]
    [(32%nat, 2^47); (33%nat, 2^47); (34%nat, 2^47); (35%nat, 2^47); (36%nat, 2^47); (37%nat, 2^47); (38%nat, 2^63); (39%nat, 2^63); (40%nat, 2^63);
     (41%nat, 2^64); (42%nat, 2^64); (43%nat, 2^64); (44%nat, 2^64); (45%nat, 2^64)] NoRegions
    [h; s; wnd; prv; hd; pb; cb; cp; n; bv_unsigned sv20; bv_unsigned sv21; bv_unsigned sv22; raDI; bv_unsigned sv23] NoVals F0 F0'
    (mkst regs0 (0x16620 : word) mem s6u_rom) R HR Hfr Hms.
  all: try (symex_auto; lia).
  all: try (change (2 ^ 3) with 8 in *; zcond_close).
  exists R. split; [exact Hms|].
  symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (2%bv : reg) as A2. symex_reg HR (8%bv : reg) as A8.
  symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18. symex_reg HR (19%bv : reg) as A19.
  symex_reg HR (20%bv : reg) as A20. symex_reg HR (21%bv : reg) as A21. symex_reg HR (22%bv : reg) as A22.
  symex_reg HR (23%bv : reg) as A23. symex_reg HR (24%bv : reg) as A24. symex_reg HR (25%bv : reg) as A25.
  symex_reg HR (26%bv : reg) as A26. symex_reg HR (27%bv : reg) as A27.
  unfold A6_RA_TI. rewrite ?zw_u in *.
  split; [exact A1|]. split; [exact A10|]. split; [exact A2|]. split; [exact A8|]. split; [exact A9|].
  split; [exact A18|]. split; [exact A19|]. split; [exact A20|]. split; [exact A21|]. split; [exact A22|].
  split; [exact A23|]. split; [exact A24|]. split; [exact A25|]. split; [exact A26|]. split; [exact A27|].
  intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.



Definition IA : simg :=
  simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put
    (I0 h wnd prv hd) 16 8 pb) 24 8 65536) 196 4 6) 200 4 0) 5888 8 (pb + 16384)) 5904 4 49149) 72 1 8)
    32 8 pb) 40 8 0) 8 4 42) 56 8 0) 76 4 (-2).   (* 1.4: s + 56 cleared by deflateResetKeep (`sd zero,56(s0)` at 0x16ea4) *)

Local Ltac simg_tower H0 :=
  lazymatch goal with
  | |- SIMG _ (wbytes ?M (zw (s + ?o)) (Z_to_le_bytes ?w ?v)) _ _ _ =>
      eapply (SIMG_store s6u_segs M s 5968 _ o w v); [simg_tower H0 | vm_compute; reflexivity | lia | lia]
  | |- SIMG _ (wbytes ?M (zw ?b) ?bs) _ _ _ =>
      eapply (SIMG_ext s6u_segs M); [simg_tower H0 | intros z Hz; change (Z_to_bv 64 z) with (zw z); apply wbytes_inside; rewrite ?length_Z_to_le_bytes; [lia | cbn; lia | rewrite u_zw_small by lia; cbn; lia] ]
  | |- SIMG _ mem _ _ _ => exact H0
  end.

Lemma simg_A : SIMG s6u_segs memA s 5968 IA.
Proof.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB.
  pose proof (u64_range sv20) as U20. pose proof (u64_range sv21) as U21. pose proof (u64_range sv22) as U22.
  pose proof (u64_range (getr regs0 23)) as U23. pose proof (u64_range (getr regs0 24)) as U24. pose proof (u64_range (getr regs0 25)) as U25.
  pose proof (u64_range (getr regs0 26)) as U26. pose proof (u64_range (getr regs0 27)) as U27.
  pose proof (u64_range sv23) as U23'.
  unfold memA, IA. simg_tower HI0.
Qed.

Definition GA : franges := [(s, 5968); (h + -192, 192); (h + 8, 104)].

Local Ltac ag_tower H0 :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold GA;
              first [ apply sub_franges_here; cbn; lia | apply sub_franges_later; apply sub_franges_here; cbn; lia
                    | do 2 apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact H0.

Lemma agree_A : agree_out GA mem memA.
Proof.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB.
  unfold memA. ag_tower (agree_out_refl GA mem).
Qed.

Lemma grows_A : forall x, mem x <> None -> memA x <> None.
Proof. intros x Hx. unfold memA. repeat apply wbytes_grows. exact Hx. Qed.

Lemma mapped_A : forall a k, mapped mem a k -> mapped memA a k.
Proof. intros a k H x Hx. apply grows_A. exact (H x Hx). Qed.

Lemma cells_A : forall P N f, cells s6u_segs mem P 1 1 N f -> 0 <= P -> P + N <= 2 ^ 64 ->
  (s + 5968 <= P \/ P + N <= s) -> (h + 112 <= P \/ P + N <= h + -192) -> cells s6u_segs memA P 1 1 N f.
Proof.
  intros P N f Hc HP0 HP1 D1 D2. pose proof agree_A as AG.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB MK MS HI0.
  apply (cells_agree_out s6u_segs GA mem memA P 1 1%nat N f AG); [| lia | lia | lia | exact Hc].
  unfold GA. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; lia.
Qed.

Lemma cellsA :
  cell s6u_segs memA (h + -8) 8 raDI /\ cell s6u_segs memA (h + -16) 8 cb /\ cell s6u_segs memA (h + -24) 8 cp
  /\ cell s6u_segs memA (h + -40) 8 A6_RA_RK /\ cell s6u_segs memA (h + -48) 8 (h + 8) /\ cell s6u_segs memA (h + -56) 8 cp
  /\ cell s6u_segs memA (h + 48) 8 0 /\ cell s6u_segs memA (h + 56) 8 0 /\ cell s6u_segs memA (h + 24) 8 0
  /\ cell s6u_segs memA (h + 96) 4 2 /\ cell s6u_segs memA (h + 104) 8 1
  /\ cell s6u_segs memA (h + 64) 8 s /\ cell s6u_segs memA (h + 72) 8 A6_ZCALLOC /\ cell s6u_segs memA (h + 80) 8 A6_ZCFREE
  /\ cell s6u_segs memA (h + 88) 8 0.
Proof.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB.
  unfold memA, A6_RA_RK, A6_ZCALLOC, A6_ZCFREE in *.
  repeat split;
    repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                  | apply cell_write_other; [| lia | cbn; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia] ]);
    assumption.
Qed.

(* 1.4: the s2 slots of deflateReset (h - 32) and deflateResetKeep (h - 64) hold n *)
Lemma cnA : cell s6u_segs memA (h + -32) 8 n /\ cell s6u_segs memA (h + -64) 8 n.
Proof.
  clear - Hh HS. unfold memA.
  split;
    repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                  | apply cell_write_other; [| lia | cbn; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia] ]).
Qed.


Definition p6 : ds_ptrs := DSP (h + 8) wnd prv hd pb.
Definition FTR : franges := [(s, 5968); (pb, 65536)].

Variables (b0 bw bp bh bb : blk) (cs : cstrm).
Local Abbreviation sRK0 := (DInit6_M.sRK0 b0 bw bp bh bb cs).
Local Abbreviation sTI0 := (DInit6_M.sTI0 b0 bw bp bh bb cs).
Local Abbreviation sLM0 := (DInit6_M.sLM0 b0 bw bp bh bb cs).

Lemma sRK0_dvals6u : forall (p : ds_ptrs) (S : Z),
  dvals6u sRK0 p S (0, 0, 0, 0, 0, 0) =
  [p_strm p; 42; p_pending_buf p; 65536; p_pending_buf p + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; p_window p; 0;
   p_prev p; p_head p; 0; 32768; 15; 32767; 5; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 6; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   p_pending_buf p + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof. clear. intros p S. unfold DInit6_M.sRK0. vnf. reflexivity. Qed.

Lemma BRH_FTR : BRH FTR s p6 65536.
Proof.
  clear - Hh HS HB DSB. unfold BRH, FTR, p6, dsl_SIZE. cbn [p_pending_buf].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply sub_franges_here; lia|]. split; [apply sub_franges_here; lia|]. split; [apply sub_franges_here; lia|].
  apply sub_franges_later. apply sub_franges_here; lia.
Qed.

Lemma FTR_S : sub_franges FTR s dsl_SIZE.
Proof. clear. unfold FTR, dsl_SIZE. apply sub_franges_here; lia. Qed.

Lemma UBT_p6 : UBT s p6.
Proof.
  clear - Hh Hh16 HS16 HS HB HW. unfold p6. split; cbn [p_pending_buf p_window p_strm]; try lia.
  - apply mod16_mod8; exact HS16.
  - apply mod16_p8_mod8; exact Hh16.
Qed.

Lemma fields_RK : fields s6u_segs memA s dsl_layout (dvals6u sRK0 p6 s (0, 0, 0, 0, 0, 0)).
Proof.
  pose proof simg_A as SA. clear - SA.
  rewrite (sRK0_dvals6u p6 s). unfold p6. cbn [p_strm p_pending_buf p_window p_prev p_head].
  apply (fields_eqm_transfer s6u_segs memA s dsl_layout (simg_vals IA dsl_layout)).
  - apply (SIMG_fields s6u_segs memA s 5968 IA dsl_layout SA). vm_compute. reflexivity.
  - unfold IA, I0. rewrite ?Z.add_0_r. set (vh := h + 8). set (vpb := pb + 16384).
    lazy -[Z.modulo Z.pow vh vpb]. repeat split; reflexivity.
Qed.

Lemma arrays_RK : dsl_arrays s6u_segs memA s sRK0.
Proof.
  pose proof simg_A as SA. clear - Hh SA HS.
  pose proof (sRK0_arrs b0 bw bp bh bb cs) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & _).
  unfold dsl_arrays. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9.
  repeat match goal with |- _ /\ _ => split end;
    (lazymatch goal with |- cells _ _ _ _ _ ?n _ => let k := eval vm_compute in (Z.to_nat n) in change n with (Z.of_nat k) end;
     eapply cells_extf; [ eapply (SIMG_cells_z s6u_segs memA s 5968 IA); [exact SA | vm_compute; reflexivity | lia | cbn; lia | cbn; lia]
                        | intros i Hi; symmetry; first [apply arr_u16_of_z0 | apply arr_s32_of_z0 | apply arr_u8_of_z0] ]).
Qed.

Lemma pend_RK : cells s6u_segs memA pb 1 1 65536 (arr_get (ds_pending_buf sRK0)).
Proof.
  pose proof (sRK0_arrs b0 bw bp bh bb cs) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E & _). rewrite E.
  eapply cells_extf; [| intros i Hi; symmetry; apply blk_bytes_z0].
  apply (cells_A pb 65536 (fun _ => 0) ZPB); [lia | lia | exact DSB | clear - Hh HB; lia].
Qed.

Lemma BRi_RK : BRi6u FTR memA s p6 65536 memA sRK0.
Proof.
  split; [exists (0, 0, 0, 0, 0, 0); exact fields_RK|].
  split; [exact arrays_RK|]. split; [exact (tree_lens_sRK0 b0 bw bp bh bb cs)|].
  unfold p6. cbn [p_pending_buf]. split; [exact pend_RK|].
  pose proof (sRK0_arrs b0 bw bp bh bb cs) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E & _). rewrite E.
  split; [unfold blk_bytes; rewrite arr_len_init; reflexivity|].
  split; [apply agree_out_refl|]. unfold dsl_SIZE.
  split; [apply mapped_A; exact MS|]. split; [apply mapped_A; exact MB|]. intros x Hx; exact Hx.
Qed.

Lemma seg_TI : forall regs,
  getr regs 10 = zw s -> getr regs 1 = zw A6_RA_TI ->
  exists R mB,
    msteps s6u_segs (mkst regs (0x1b6d0 : word) memA s6u_rom) (mkst R (0x16f24 : word) mB s6u_rom)
    /\ BR6u FTR memA s p6 65536 mB sTI0
    /\ (forall r : reg, reg_in r TI_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs Q10 Q1. pose proof BRH_FTR as HL. pose proof FTR_S as HFS. pose proof BRi_RK as HBRi. pose proof UBT_p6 as HU.
  clear - Q10 Q1 HL HFS HBRi HU.
  destruct (tr_init_run6u_ok FTR memA memA s p6 65536 sRK0 (zw A6_RA_TI) regs HL HFS
              ltac:(unfold A6_RA_TI; apply ret_ok_zw; [lia | reflexivity]) HBRi HU Q10 Q1) as (R & mB & Hms & HBR & Hfr).
  exists R, mB. unfold TrApi6u.A6U_TR_INIT, A6_RA_TI in *.
  replace (zw 0x1b6d0) with (0x1b6d0%bv : word) in Hms by (apply bv_eq; reflexivity).
  replace (zw 0x16f24) with (0x16f24%bv : word) in Hms by (apply bv_eq; reflexivity).
  split; [exact Hms|]. split; [rewrite (sTI0_eq b0 bw bp bh bb cs); exact HBR | exact Hfr].
Qed.



Lemma sTI0_vals6u : forall (p : ds_ptrs) (S : Z),
  ds6u_vals sTI0 p S =
  [p_strm p; 42; p_pending_buf p; 65536; p_pending_buf p + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; p_window p; 0;
   p_prev p; p_head p; 0; 32768; 15; 32767; 5; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 6; 0; 0; 0;
   S + 212; 0; 180992; S + 2504; 0; 181024; S + 2748; 0; 181056; 0; 0;
   p_pending_buf p + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof. clear. intros p S. unfold DInit6_M.sTI0, ds6u_vals. vnf. reflexivity. Qed.

Lemma sLM0_vals6u : forall (p : ds_ptrs) (S : Z),
  ds6u_vals sLM0 p S =
  [p_strm p; 42; p_pending_buf p; 65536; p_pending_buf p + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; p_window p; 65536;
   p_prev p; p_head p; 0; 32768; 15; 32767; 5; 0; 2; 0; 0; 0; 0; 0; 2; 128; 16; 6; 0; 8; 128;
   S + 212; 0; 180992; S + 2504; 0; 181024; S + 2748; 0; 181056; 0; 0;
   p_pending_buf p + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof. clear. intros p S. unfold DInit6_M.sLM0, ds6u_vals. vnf. reflexivity. Qed.

Hypothesis MEMSET : memset_run6u.



(* 1.4 UBSan: deflateResetKeep's tail now stores matches := s2 (= 0, S + 5928), block_start := strstart (0),
   match_length := 2, match_available := 0, lookahead := 0, prev_length := 2 before lm_init redoes them *)
Definition memC (mB : word -> option byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mB
    (zw (s + 5928)) (Z_to_le_bytes 4 0))
    (zw (s + 152)) (Z_to_le_bytes 8 0))
    (zw (s + 160)) (Z_to_le_bytes 4 2))
    (zw (s + 168)) (Z_to_le_bytes 4 0))
    (zw (s + 180)) (Z_to_le_bytes 4 0))
    (zw (s + 184)) (Z_to_le_bytes 4 2))
    (zw (s + 104)) (Z_to_le_bytes 8 65536))
    (zw (hd + 65534)) (Z_to_le_bytes 2 0).

Lemma seg_B : forall regs mB,
  getr regs 2 = zw (h + -64) -> getr regs 8 = zw s -> getr regs 9 = zw (h + 8) -> getr regs 18 = zw 0 ->
  cell s6u_segs mB (s + 120) 8 hd -> cell s6u_segs mB (s + 132) 4 32768 -> cell s6u_segs mB (s + 80) 4 32768 -> cell s6u_segs mB (s + 172) 4 0 ->
  cell s6u_segs mB (h + 64) 8 s -> cell s6u_segs mB (h + -40) 8 A6_RA_RK -> cell s6u_segs mB (h + -48) 8 (h + 8) ->
  cell s6u_segs mB (h + -56) 8 cp -> cell s6u_segs mB (h + -64) 8 n ->
  mapped mB s 5968 -> mapped mB hd 65536 ->
  exists R,
    msteps s6u_segs (mkst regs (0x16f24 : word) mB s6u_rom) (mkst R (0x2ac28 : word) (memC mB) s6u_rom)
    /\ getr R 1 = zw A6_RA_MS /\ getr R 10 = zw hd /\ getr R 11 = zw 0 /\ getr R 12 = zw 65534
    /\ getr R 2 = zw (h + -32) /\ getr R 8 = zw s /\ getr R 9 = zw (s + 5928) /\ getr R 18 = zw 0
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs mB Q2 Q8 Q9 Q18 C120 C132 C80 C172 C56 F40 F48 F56 F64 MSB MHB.
  clear HSi HWi HPi HHi HBi DSW DSQ DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB MK MS HI0 HROM
        Cra Ccb Ccp Cn Cdl C20 C21 C22 C23 Z56 Z64 Z72 Z80 Z48 MEMSET P2 P8 P9 P10 P21 P18 P19 P20 P22.
  unfold mapped in MSB, MHB. unfold A6_RA_RK in *. unfold memC.
  pose proof (mod16_mod8 s HS16) as US8. pose proof (mod16_p8_mod8 h Hh16) as UH8. pose proof (mod16_p65534_mod2 hd HHD16) as UHD2.
  (* 1.4: reads strstart (0), then the epilogue's ra / s0 / s1 / s2, then deflateReset's lm_init reads *)
  symex s6u_segs iC 60%nat [true; false; false; false; false; false; false; false; false]
    [RVal (ELit 0); RVal (ELit 0x16890); RVal (EAdd (EVar 32) (ELit 8)); RVal (EVar 35); RVal (EVar 36);
     RVal (EVar 33); RVal (ELit 32768); RVal (ELit 32768); RVal (EVar 34)]
    [(2, EAdd (EVar 32) (ELit (-64))); (8, EVar 33); (9, EAdd (EVar 32) (ELit 8)); (18, ELit 0)]
    [(32%nat, 2^47); (33%nat, 2^47); (34%nat, 2^47); (35%nat, 2^63); (36%nat, 2^63)] NoRegions
    [h; s; hd; cp; n] NoVals F0 F0' (mkst regs (0x16f24 : word) mB s6u_rom) R HR Hfr Hms.
  all: try (symex_auto; lia).
  all: try (change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close).
  exists R. split; [exact Hms|].
  symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11. symex_reg HR (12%bv : reg) as A12.
  symex_reg HR (2%bv : reg) as A2. symex_reg HR (8%bv : reg) as A8. symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18.
  unfold A6_RA_MS. rewrite ?zw_u in *.
  split; [exact A1|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12|].
  split; [exact A2|]. split; [exact A8|]. split; [first [exact A9 | rewrite A9; f_equal; lia]|]. split; [exact A18|].
  intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.


Lemma seg_MS : forall regs m,
  getr regs 1 = zw A6_RA_MS -> getr regs 10 = zw hd -> getr regs 11 = zw 0 -> getr regs 12 = zw 65534 ->
  mapped m hd 65536 ->
  exists R m',
    msteps s6u_segs (mkst regs (0x2ac28 : word) m s6u_rom) (mkst R (0x1692c : word) m' s6u_rom)
    /\ getr R 10 = zw hd
    /\ (forall r : reg, reg_in r memset_clob = false -> getr R r = getr regs r)
    /\ filled m' hd (hd + 65534) (ms_bb 0)
    /\ same_outside m m' hd (hd + 65534)
    /\ (forall x, m x <> None -> m' x <> None).
Proof.
  intros regs m Q1 Q10 Q11 Q12 HM.
  clear - Hh HHD MEMSET Q1 Q10 Q11 Q12 HM.
  destruct (MEMSET m regs hd 0 65534 (zw A6_RA_MS) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (mapped_sub m hd 65536 hd 65534 HM ltac:(lia) ltac:(lia))
              ltac:(unfold A6_RA_MS; apply ret_ok_zw; [lia | reflexivity]) Q1 Q10 Q11 Q12)
    as (R & m' & Hms & A10 & Hfr & Hfill & Hso & Hgr).
  exists R, m'. unfold A6_RA_MS in *.
  replace (zw A6U_MEMSET) with (0x2ac28%bv : word) in Hms by (apply bv_eq; reflexivity).
  replace (zw 0x1692c) with (0x1692c%bv : word) in Hms by (apply bv_eq; reflexivity).
  repeat (split; [assumption|]). exact Hgr.
Qed.


(* 1.4 UBSan: lm_init (in deflateReset) now zeroes matches (S + 5928) and slid (S + 5960) before insert *)
Definition memE (mD : word -> option byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mD
    (zw (s + 5928)) (Z_to_le_bytes 4 0))
    (zw (s + 5960)) (Z_to_le_bytes 4 0))
    (zw (s + 5932)) (Z_to_le_bytes 4 0))
    (zw (s + 180)) (Z_to_le_bytes 4 0))
    (zw (s + 184)) (Z_to_le_bytes 4 2))
    (zw (s + 188)) (Z_to_le_bytes 4 128))
    (zw (s + 192)) (Z_to_le_bytes 4 16))
    (zw (s + 204)) (Z_to_le_bytes 4 8))
    (zw (s + 208)) (Z_to_le_bytes 4 128))
    (zw (s + 128)) (Z_to_le_bytes 4 0))
    (zw (s + 152)) (Z_to_le_bytes 8 0))
    (zw (s + 160)) (Z_to_le_bytes 4 2))
    (zw (s + 168)) (Z_to_le_bytes 8 0).

Lemma seg_C : forall regs mD,
  getr regs 2 = zw (h + -32) -> getr regs 8 = zw s -> getr regs 9 = zw (s + 5928) -> getr regs 18 = zw 0 ->
  cell s6u_segs mD (h + -32) 8 n ->
  cell s6u_segs mD (s + 196) 4 6 ->
  cell s6u_segs mD (0 + 180848) 2 8 -> cell s6u_segs mD (0 + 180850) 2 16 ->
  cell s6u_segs mD (0 + 180852) 2 128 -> cell s6u_segs mD (0 + 180854) 2 128 ->
  cell s6u_segs mD (h + -8) 8 raDI -> cell s6u_segs mD (h + -16) 8 cb -> cell s6u_segs mD (h + -24) 8 cp ->
  mapped mD s 5968 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1692c : word) mD s6u_rom) (mkst R (zw raDI) (memE mD) s6u_rom)
    /\ getr R 10 = zw 0 /\ getr R 2 = zw h /\ getr R 8 = zw cb /\ getr R 9 = zw cp /\ getr R 18 = zw n
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs mD Q2 Q8 Q9 Q18 Fn C196 G0 G2 G4 G6 F8 F16 F24 MSD.
  clear HWi HPi HHi HBi DSW DSQ DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB MK MS HI0 HROM
        Cra Ccb Ccp Cn Cdl C20 C21 C22 C23 Z56 Z64 Z72 Z80 Z48 MEMSET P2 P8 P9 P10 P21 P18 P19 P20 P22.
  unfold mapped in MSD. unfold memE.
  (* 1.4: s1 = S + 5928 (matches / slid / insert stores), s2 = 0 (the return value); the epilogue reloads s2 = n *)
  symex s6u_segs iC2 60%nat [false; false]
    [RVal (ELit 6); RVal (ELit 8); RVal (ELit 16); RVal (ELit 128); RVal (ELit 128); RVal (EVar 36); RVal (EVar 34); RVal (EVar 35); RVal (EVar 37)]
    [(2, EAdd (EVar 32) (ELit (-32))); (8, EVar 33); (9, EAdd (EVar 33) (ELit 5928)); (18, ELit 0)]
    [(32%nat, 2^47); (33%nat, 2^47); (34%nat, 2^63); (35%nat, 2^63); (36%nat, 2^64); (37%nat, 2^63)] NoRegions
    [h; s; cb; cp; raDI; n] NoVals F0 F0' (mkst regs (0x1692c : word) mD s6u_rom) R HR Hfr Hms.
  all: try (symex_auto; lia).
  all: try (rewrite (land_m2_even raDI) by (exact (proj2 HraDI)); reflexivity).
  all: try zcond_close.
  exists R. split; [exact Hms|].
  symex_reg HR (10%bv : reg) as A10. symex_reg HR (2%bv : reg) as A2. symex_reg HR (8%bv : reg) as A8. symex_reg HR (9%bv : reg) as A9.
  symex_reg HR (18%bv : reg) as A18.
  rewrite ?zw_u in *. rewrite ?Z.add_0_r in A2.
  split; [exact A10|]. split; [first [exact A2 | rewrite A2; f_equal; lia]|]. split; [exact A8|]. split; [exact A9|]. split; [exact A18|].
  intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.



Definition GB : franges := [(s + 104, 8); (hd, 65536); (s + 152, 20); (s + 180, 8); (s + 5928, 4)].
Definition GC : franges := [(s + 128, 84); (s + 5928, 8); (s + 5960, 4)].
Definition GX : franges := [(s, 5968); (pb, 65536); (hd, 65536)].
Definition GI : franges := [(s, 5968); (pb, 65536); (hd, 65536); (h + -192, 192); (h + 8, 104)].

Definition INITPOST (mF : word -> option byte) : Prop :=
  ds6u_scalars mF s p6 sLM0 /\ ds6u_arrays mF s sLM0 /\ tree_lens sLM0
  /\ ds6u_windowA mF p6 sLM0 /\ ds6u_prevA mF p6 sLM0 /\ ds6u_headA mF p6 sLM0 /\ ds6u_pendA mF p6 sLM0
  /\ (cell s6u_segs mF (h + 24) 8 0 /\ cell s6u_segs mF (h + 48) 8 0 /\ cell s6u_segs mF (h + 56) 8 0
      /\ cell s6u_segs mF (h + 64) 8 s /\ cell s6u_segs mF (h + 72) 8 A6_ZCALLOC /\ cell s6u_segs mF (h + 80) 8 A6_ZCFREE
      /\ cell s6u_segs mF (h + 88) 8 0 /\ cell s6u_segs mF (h + 96) 4 2 /\ cell s6u_segs mF (h + 104) 8 1)
  /\ agree_out GI mem mF
  /\ (forall x, mem x <> None -> mF x <> None)
  /\ rom_clear mF 0x10000 0x2c3f8.

Local Ltac disj := unfold disj_franges, GB, GC, GX, GI, FTR, GA; cbn [in_franges]; intros ? ?; lia.
Local Ltac subf := unfold GB, GC, GX, GI; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?length_Z_to_le_bytes;
                   repeat (first [apply sub_franges_here; cbn; lia | apply sub_franges_later]).


Lemma rom_A : rom_clear memA 0x10000 0x2c3f8.
Proof.
  pose proof agree_A as AG.
  clear - AG HROM MK MS Hh HS HSi.
  apply (rom_clear_agree GA mem memA _ _ HROM AG).
  unfold GA. cbn [in_franges]. intros x [Hx|[Hx|[Hx|[]]]]; [apply MS; lia | apply MK; lia | apply MK; lia].
Qed.

Section POST.
Variables (mB mD : word -> option byte).
Hypothesis HBR : BR6u FTR memA s p6 65536 mB sTI0.
Hypothesis Hfill : filled mD hd (hd + 65534) (ms_bb 0).
Hypothesis Hso : same_outside (memC mB) mD hd (hd + 65534).
Hypothesis Hgr : forall x, memC mB x <> None -> mD x <> None.

Lemma fields_B : fields s6u_segs mB s dsl_layout
  [h + 8; 42; pb; 65536; pb + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; wnd; 0;
   prv; hd; 0; 32768; 15; 32767; 5; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 6; 0; 0; 0;
   s + 212; 0; 180992; s + 2504; 0; 181024; s + 2748; 0; 181056; 0; 0;
   pb + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof.
  destruct HBR as (Fd & _). clear - Fd.
  change (fields s6u_segs mB s dsl_layout (ds6u_vals sTI0 p6 s)) in Fd.
  rewrite (sTI0_vals6u p6 s) in Fd. exact Fd.
Qed.

Lemma mapped_B : mapped mB s 5968 /\ mapped mB hd 65536 /\ mapped mB pb 65536.
Proof.
  destruct HBR as (_ & _ & _ & _ & _ & _ & M1 & M2 & G). clear - M1 M2 G MH.
  split; [exact M1|]. split; [| exact M2].
  intros x Hx. apply G. apply (mapped_A hd 65536 MH x Hx).
Qed.

Lemma agree_2 : agree_out FTR memA mB.
Proof. destruct HBR as (_ & _ & _ & _ & _ & AG & _). exact AG. Qed.

Lemma mB_facts :
  cell s6u_segs mB (s + 120) 8 hd /\ cell s6u_segs mB (s + 132) 4 32768 /\ cell s6u_segs mB (s + 80) 4 32768 /\ cell s6u_segs mB (s + 172) 4 0
  /\ cell s6u_segs mB (h + 64) 8 s /\ cell s6u_segs mB (h + -40) 8 A6_RA_RK /\ cell s6u_segs mB (h + -48) 8 (h + 8)
  /\ cell s6u_segs mB (h + -56) 8 cp /\ cell s6u_segs mB (h + -64) 8 n.
Proof.
  pose proof fields_B as F. pose proof agree_2 as AG.
  pose proof cellsA
    as (_ & _ & _ & X40 & X48 & X56 & _ & _ & _ & _ & _ & X64 & _).
  pose proof cnA as (_ & X64n).
  clear - F AG X40 X48 X56 X64 X64n Hh HS HB.
  split; [exact (fields_nth s6u_segs mB s _ _ 17 120 8%nat _ F eq_refl eq_refl)|].
  split; [exact (fields_nth s6u_segs mB s _ _ 19 132 4%nat _ F eq_refl eq_refl)|].
  split; [exact (fields_nth s6u_segs mB s _ _ 11 80 4%nat _ F eq_refl eq_refl)|].
  split; [exact (fields_nth s6u_segs mB s _ _ 27 172 4%nat _ F eq_refl eq_refl)|].
  repeat match goal with |- _ /\ _ => split end;
    (eapply (cell_agree_out s6u_segs FTR memA mB _ _ _ AG); [disj | lia | cbn; lia | assumption]).
Qed.

Lemma agree_B : agree_out GB mB (memC mB).
Proof.
  clear - Hh HS HHD. unfold memC.
  repeat (apply agree_out_wbytes; [| lia | rewrite length_Z_to_le_bytes; cbn; lia | subf]). apply agree_out_refl.
Qed.

Lemma agree_MS : agree_out [(hd, 65536)] (memC mB) mD.
Proof.
  clear - Hh Hso HHD. apply (same_outside_agree_out (memC mB) mD hd (hd + 65534)). exact Hso.
  intros x Hx. cbn. lia.
Qed.

Lemma agree_BD : agree_out GB mB mD.
Proof.
  pose proof agree_B as A1. pose proof agree_MS as A2. clear - A1 A2.
  apply (agree_out_trans GB mB (memC mB) mD A1).
  apply (agree_out_weaken [(hd, 65536)] GB _ _ A2). unfold GB. cbn [in_franges]. intros x Hx. tauto.
Qed.

Lemma agree_E : agree_out GC mD (memE mD).
Proof.
  clear - Hh HS. unfold memE.
  repeat (apply agree_out_wbytes; [| lia | rewrite length_Z_to_le_bytes; cbn; lia | subf]). apply agree_out_refl.
Qed.

Lemma agree_AD : agree_out GX memA mD.
Proof.
  pose proof agree_2 as A1. pose proof agree_BD as A2. clear - Hh A1 A2 HS.
  apply (agree_out_trans GX memA mB mD).
  - apply (agree_out_weaken FTR GX _ _ A1). unfold FTR, GX. cbn [in_franges]. intros x Hx. tauto.
  - apply (agree_out_weaken GB GX _ _ A2). unfold GB, GX. cbn [in_franges]. intros x Hx. lia.
Qed.

Lemma agree_AE : agree_out GX memA (memE mD).
Proof.
  pose proof agree_AD as A1. pose proof agree_E as A2. clear - Hh A1 A2 HS.
  apply (agree_out_trans GX memA mD (memE mD) A1).
  apply (agree_out_weaken GC GX _ _ A2). unfold GC, GX. cbn [in_franges]. intros x Hx. lia.
Qed.

Lemma grows_D : forall x, mem x <> None -> mD x <> None.
Proof.
  destruct HBR as (_ & _ & _ & _ & _ & _ & _ & _ & G). intros x Hx. apply Hgr. unfold memC.
  repeat apply wbytes_grows. apply G. apply grows_A. exact Hx.
Qed.

Lemma grows_E : forall x, mem x <> None -> memE mD x <> None.
Proof. intros x Hx. unfold memE. repeat apply wbytes_grows. exact (grows_D x Hx). Qed.

Lemma mapped_D : mapped mD s 5968 /\ mapped mD hd 65536.
Proof.
  destruct mapped_B as (M1 & M2 & _). clear - M1 M2 Hgr.
  split; intros x Hx; apply Hgr; unfold memC; repeat apply wbytes_grows; [exact (M1 x Hx) | exact (M2 x Hx)].
Qed.

Lemma rom_B : rom_clear mB 0x10000 0x2c3f8.
Proof.
  pose proof rom_A as R. pose proof agree_2 as AG. pose proof mapped_A as M.
  clear - Hh R AG M MS MB HS HB.
  apply (rom_clear_agree FTR memA mB _ _ R AG).
  unfold FTR. cbn [in_franges]. intros x [Hx|[Hx|[]]]; [apply (M _ _ MS); lia | apply (M _ _ MB); lia].
Qed.

Lemma rom_D : rom_clear mD 0x10000 0x2c3f8.
Proof.
  pose proof rom_B as R. pose proof agree_MS as AG. destruct mapped_B as (M1 & M2 & _).
  clear - Hh R AG M1 M2 HS HHD.
  apply (rom_clear_agree [(hd, 65536)] (memC mB) mD _ _); [| exact AG |].
  - unfold memC. repeat (apply rom_clear_wbytes; rewrite ?length_Z_to_le_bytes;
      [| intros x Hx; cbn in Hx; repeat apply wbytes_grows; first [apply M1; lia | apply M2; lia] | lia | cbn; lia]).
    exact R.
  - cbn [in_franges]. intros x [Hx|[]]. unfold memC. repeat apply wbytes_grows. apply M2. lia.
Qed.

Lemma rom_E : rom_clear (memE mD) 0x10000 0x2c3f8.
Proof.
  pose proof rom_D as R. destruct mapped_D as (M1 & _). clear - Hh R M1 HS. unfold memE.
  repeat (apply rom_clear_wbytes; rewrite ?length_Z_to_le_bytes;
          [| intros x Hx; cbn in Hx; repeat apply wbytes_grows; apply M1; lia | lia | cbn; lia]).
  exact R.
Qed.

(* 1.4: field indices for the deflateResetKeep tail (5928, 104, 152, 160, 168,
   180, 184) and lm_init stores; slid (S + 5960) is a gap of dsl_layout *)
Local Ltac kof o :=
  lazymatch o with
  | 5928 => constr:(54%nat) | 104 => constr:(15%nat) | 5932 => constr:(55%nat) | 180 => constr:(29%nat) | 184 => constr:(30%nat) | 188 => constr:(31%nat)
  | 192 => constr:(32%nat) | 204 => constr:(35%nat) | 208 => constr:(36%nat) | 128 => constr:(18%nat)
  | 152 => constr:(23%nat) | 160 => constr:(24%nat) | 168 => constr:(26%nat) | 172 => constr:(27%nat)
  end.

Local Ltac fw_tower Hf M :=
  lazymatch M with
  | wbytes ?M1 (zw (s + 5960)) (Z_to_le_bytes 4 ?v) =>
      fw_tower Hf M1;
      lazymatch goal with
      | H1 : fields s6u_segs M1 s dsl_layout ?vs |- _ =>
          let H2 := fresh "HF" in
          pose proof (DSLayout.fields_write_gap s6u_segs M1 s dsl_layout vs dsl_SIZE 5960 (Z_to_le_bytes 4 v) H1
                        dsl_layout_within ltac:(rewrite length_Z_to_le_bytes; vm_compute; reflexivity)
                        ltac:(lia) ltac:(unfold dsl_SIZE; lia) ltac:(lia)
                        ltac:(rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia)) as H2;
          clear H1
      end
  | wbytes ?M1 (zw (s + ?o)) (Z_to_le_bytes ?w ?v) =>
      fw_tower Hf M1;
      lazymatch goal with
      | H1 : fields s6u_segs M1 s dsl_layout ?vs |- _ =>
          let k := kof o in
          let H2 := fresh "HF" in
          pose proof (fields_write_field s6u_segs M1 s dsl_layout vs dsl_SIZE k o w v H1 eq_refl
                        ltac:(vm_compute; reflexivity) dsl_layout_within ltac:(lia) ltac:(unfold dsl_SIZE; lia)) as H2;
          cbn [list_upd] in H2; clear H1
      end
  | _ => let H := fresh "HF" in pose proof Hf as H
  end.

(* 1.4: deflateResetKeep's tail sets match_length (index 24) and prev_length (index 30) to 2, window_size (15) to 65536 *)
Lemma fields_D : fields s6u_segs mD s dsl_layout
  [h + 8; 42; pb; 65536; pb + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; wnd; 65536;
   prv; hd; 0; 32768; 15; 32767; 5; 0; 2; 0; 0; 0; 0; 0; 2; 0; 0; 6; 0; 0; 0;
   s + 212; 0; 180992; s + 2504; 0; 181024; s + 2748; 0; 181056; 0; 0;
   pb + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof.
  pose proof fields_B as F. pose proof agree_MS as AG. clear - Hh F AG HS HHD DSH.
  apply (fields_agree_out s6u_segs [(hd, 65536)] (memC mB) mD s dsl_layout _ dsl_SIZE); [| exact dsl_layout_within | exact AG | unfold dsl_SIZE; disj | lia | unfold dsl_SIZE; lia].
  unfold memC. apply (fields_write_other s6u_segs _ s dsl_layout _ dsl_SIZE); rewrite ?length_Z_to_le_bytes;
    [| exact dsl_layout_within | lia | unfold dsl_SIZE; lia | lia | cbn; lia | unfold dsl_SIZE; cbn; lia].
  lazymatch goal with |- fields _ ?M _ _ _ => fw_tower F M end.
  match goal with H : fields _ _ _ _ _ |- _ => exact H end.
Qed.

(* 1.4 UBSan: lm_init stores matches (5928), slid (5960) and insert (5932) as three separate words; 168 is one sd *)
Lemma fields_E : ds6u_scalars (memE mD) s p6 sLM0.
Proof.
  pose proof fields_D as F. clear - Hh F HS.
  unfold ds6u_scalars, ds6u_layout. rewrite (sLM0_vals6u p6 s). cbn [p_strm p_pending_buf p_window p_prev p_head].
  unfold memE. rewrite (wsplit8 _ (s + 168)). replace (s + 168 + 4) with (s + 172) by lia.
  lazymatch goal with |- fields _ ?M _ _ _ => fw_tower F M end.
  match goal with H : fields _ _ _ _ _ |- _ => exact H end.
Qed.

Lemma arrays_E : ds6u_arrays (memE mD) s sLM0.
Proof.
  destruct HBR as (_ & Ar & _). pose proof agree_BD as A1. pose proof agree_E as A2. clear - Hh Ar A1 A2 HS HHD DSH.
  pose proof (sLM0_trees b0 bw bp bh bb cs) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & _).
  unfold ds6u_arrays, dsl_arrays. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. fold (dsl_arrays s6u_segs (memE mD) s sTI0).
  apply (arrays_agree_out s6u_segs GC mD (memE mD) s sTI0); [| exact A2 | disj | disj | disj | lia | unfold dsl_SIZE; lia].
  apply (arrays_agree_out s6u_segs GB mB mD s sTI0); [exact Ar | exact A1 | disj | disj | disj | lia | unfold dsl_SIZE; lia].
Qed.

Lemma window_E : ds6u_windowA (memE mD) p6 sLM0.
Proof.
  pose proof agree_AE as AG. pose proof (cells_A wnd 65536 _ ZW) as C.
  clear - AG C Hh HS HW HHD HB DSW DWH DWB.
  unfold ds6u_windowA. rewrite (proj1 (sLM0_lens b0 bw bp bh bb cs)). unfold p6. cbn [p_window].
  eapply cells_extf; [| intros i Hi; symmetry; apply sLM0_window_get].
  eapply (cells_agree_out s6u_segs GX memA (memE mD) wnd 1 1 65536 _ AG); [disj | cbn; lia | lia | lia |].
  apply C; lia.
Qed.

Lemma prev_E : ds6u_prevA (memE mD) p6 sLM0.
Proof.
  pose proof agree_AE as AG. pose proof (cells_A prv 65536 _ ZPV) as C.
  clear - AG C Hh HS HP HHD HB DSQ DPH DPB.
  unfold ds6u_prevA. rewrite (proj1 (proj2 (sLM0_lens b0 bw bp bh bb cs))). unfold p6. cbn [p_prev].
  eapply cells_extf; [| intros i Hi; symmetry; apply sLM0_prev_get].
  apply cells2_zero; [| lia | lia].
  eapply (cells_agree_out s6u_segs GX memA (memE mD) prv 1 1 (2 * 32768) _ AG); [disj | cbn; lia | lia | lia |].
  apply C; lia.
Qed.

Lemma head_D : cells s6u_segs mD hd 1 1 65536 (fun _ => 0).
Proof.
  pose proof agree_2 as AG. pose proof (cells_A hd 65536 _ ZHD) as C.
  clear - AG C Hfill Hso Hh HS HHD HB DSH DHB.
  assert (C1 : cells s6u_segs mB hd 1 1 65536 (fun _ => 0)).
  { eapply (cells_agree_out s6u_segs FTR memA mB hd 1 1 65536 _ AG); [disj | cbn; lia | lia | lia |]. apply C; lia. }
  assert (C2 : cells s6u_segs (memC mB) hd 1 1 65536 (fun _ => 0)).
  { unfold memC. eapply cells_extf.
    - replace (hd + 65534) with (hd + 65534) by reflexivity.
      apply (cells_wbytes_bytes s6u_segs _ hd 65536 (fun _ => 0) 65534 (Z_to_le_bytes 2 0));
        [| lia | cbn; lia | lia | lia].
      repeat (apply cells_write_other; rewrite ?length_Z_to_le_bytes; [| solve [cbn; lia] .. ]). exact C1.
    - intros i Hi. cbn beta.
      destruct (Z.leb_spec 65534 i); cbn [andb]; [|reflexivity].
      destruct (Z.ltb_spec i (65534 + Z.of_nat (length (Z_to_le_bytes 2 0)))) as [H0|H0]; [|reflexivity].
      rewrite length_Z_to_le_bytes in H0. cbn in H0.
      assert (E : Z.to_nat (i - 65534) = 0%nat \/ Z.to_nat (i - 65534) = 1%nat) by lia.
      destruct E as [E|E]; rewrite E; reflexivity. }
  pose proof (cells_filled0 s6u_segs (memC mB) mD hd 65536 (fun _ => 0) 0 65534) as L.
  rewrite !Z.add_0_r in L. cbn [Z.add] in L.
  eapply cells_extf; [apply L; [exact C2 | exact Hfill | exact Hso | lia | lia | lia | lia | lia] |].
  intros i Hi. cbn beta. destruct (_ && _); reflexivity.
Qed.

Lemma head_E : ds6u_headA (memE mD) p6 sLM0.
Proof.
  pose proof agree_E as AG. pose proof head_D as C. clear - Hh AG C HS HHD DSH.
  unfold ds6u_headA. rewrite (proj1 (proj2 (proj2 (sLM0_lens b0 bw bp bh bb cs)))). unfold p6. cbn [p_head].
  eapply cells_extf; [| intros i Hi; symmetry; apply sLM0_head_get].
  apply cells2_zero; [| lia | lia].
  eapply (cells_agree_out s6u_segs GC mD (memE mD) hd 1 1 (2 * 32768) _ AG); [disj | cbn; lia | lia | lia | exact C].
Qed.

Lemma pend_E : ds6u_pendA (memE mD) p6 sLM0.
Proof.
  destruct HBR as (_ & _ & _ & Cpb & _). pose proof agree_BD as A1. pose proof agree_E as A2. clear - Hh Cpb A1 A2 HS HHD HB DSB DHB.
  unfold ds6u_pendA. rewrite (proj2 (proj2 (proj2 (sLM0_lens b0 bw bp bh bb cs)))). unfold p6 in *. cbn [p_pending_buf] in *.
  pose proof (sLM0_trees b0 bw bp bh bb cs) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E). rewrite E.
  eapply (cells_agree_out s6u_segs GC mD (memE mD) pb 1 1 65536 _ A2); [disj | cbn; lia | lia | lia |].
  eapply (cells_agree_out s6u_segs GB mB mD pb 1 1 65536 _ A1); [disj | cbn; lia | lia | lia | exact Cpb].
Qed.

Lemma zcells_E :
  cell s6u_segs (memE mD) (h + 24) 8 0 /\ cell s6u_segs (memE mD) (h + 48) 8 0 /\ cell s6u_segs (memE mD) (h + 56) 8 0
  /\ cell s6u_segs (memE mD) (h + 64) 8 s /\ cell s6u_segs (memE mD) (h + 72) 8 A6_ZCALLOC /\ cell s6u_segs (memE mD) (h + 80) 8 A6_ZCFREE
  /\ cell s6u_segs (memE mD) (h + 88) 8 0 /\ cell s6u_segs (memE mD) (h + 96) 4 2 /\ cell s6u_segs (memE mD) (h + 104) 8 1.
Proof.
  pose proof agree_AE as AG.
  pose proof cellsA
    as (_ & _ & _ & _ & _ & _ & X48 & X56 & X24 & X96 & X104 & X64 & X72 & X80 & X88).
  clear - AG X48 X56 X24 X96 X104 X64 X72 X80 X88 Hh HS HHD HB.
  repeat match goal with |- _ /\ _ => split end;
    (eapply (cell_agree_out s6u_segs GX memA (memE mD) _ _ _ AG); [disj | lia | cbn; lia | assumption]).
Qed.

Lemma mD_facts :
  cell s6u_segs mD (s + 196) 4 6
  /\ cell s6u_segs mD (0 + 180848) 2 8 /\ cell s6u_segs mD (0 + 180850) 2 16
  /\ cell s6u_segs mD (0 + 180852) 2 128 /\ cell s6u_segs mD (0 + 180854) 2 128
  /\ cell s6u_segs mD (h + -8) 8 raDI /\ cell s6u_segs mD (h + -16) 8 cb /\ cell s6u_segs mD (h + -24) 8 cp
  /\ cell s6u_segs mD (h + -32) 8 n.
Proof.
  pose proof fields_D as F. pose proof rom_D as R. pose proof agree_AD as AG.
  pose proof cellsA
    as (X8 & X16 & X24 & _).
  pose proof cnA as (X32 & _).
  clear - F R AG X8 X16 X24 X32 Hh HS HHD HB.
  split; [exact (fields_nth s6u_segs mD s _ _ 33 196 4%nat _ F eq_refl eq_refl)|].
  split; [apply (rom_cell mD (0 + 180848) 2 8 R); [lia | cbn; lia | vm_compute; reflexivity]|].
  split; [apply (rom_cell mD (0 + 180850) 2 16 R); [lia | cbn; lia | vm_compute; reflexivity]|].
  split; [apply (rom_cell mD (0 + 180852) 2 128 R); [lia | cbn; lia | vm_compute; reflexivity]|].
  split; [apply (rom_cell mD (0 + 180854) 2 128 R); [lia | cbn; lia | vm_compute; reflexivity]|].
  repeat match goal with |- _ /\ _ => split end;
    (eapply (cell_agree_out s6u_segs GX memA mD _ _ _ AG); [disj | lia | cbn; lia | assumption]).
Qed.

Lemma agree_I : agree_out GI mem (memE mD).
Proof.
  pose proof agree_A as A1. pose proof agree_AE as A2.
  clear - A1 A2.
  apply (agree_out_trans GI mem memA (memE mD)).
  - apply (agree_out_weaken GA GI _ _ A1). unfold GA, GI. cbn [in_franges]. intros x Hx. tauto.
  - apply (agree_out_weaken GX GI _ _ A2). unfold GX, GI. cbn [in_franges]. intros x Hx. tauto.
Qed.

Lemma post_E : INITPOST (memE mD).
Proof.
  split; [exact fields_E|]. split; [exact arrays_E|]. split; [exact (tree_lens_sLM0 b0 bw bp bh bb cs)|].
  split; [exact window_E|]. split; [exact prev_E|]. split; [exact head_E|]. split; [exact pend_E|].
  split; [exact zcells_E|]. split; [exact agree_I|]. split; [exact grows_E | exact rom_E].
Qed.
End POST.


Definition INIT_CLOB : list reg :=
  [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Local Ltac keep_thru Hfr := rewrite Hfr by reflexivity.

Theorem ds_init_run :
  exists R mF,
    msteps s6u_segs (mkst regs0 (0x16620 : word) mem s6u_rom) (mkst R (zw raDI) mF s6u_rom)
    /\ getr R 10 = zw 0 /\ getr R 2 = zw h /\ getr R 8 = zw cb /\ getr R 9 = zw cp
    /\ getr R 18 = zw n /\ getr R 19 = zw A6_DATALEN
    /\ getr R 20 = sv20 /\ getr R 21 = sv21 /\ getr R 22 = sv22
    /\ getr R 23 = sv23 /\ getr R 24 = getr regs0 24 /\ getr R 25 = getr regs0 25 /\ getr R 26 = getr regs0 26 /\ getr R 27 = getr regs0 27
    /\ (forall r : reg, reg_in r INIT_CLOB = false -> getr R r = getr regs0 r)
    /\ INITPOST mF.
Proof.
  destruct seg_A as (R1 & Hms1 & A1 & A10 & A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & Hfr1).
  destruct (seg_TI R1 A10 A1) as (R2 & mB & Hms2 & HBR & Hfr2).
  destruct (mB_facts mB HBR) as (C120 & C132 & C80 & C172 & C56 & F40 & F48 & F56 & F64).
  destruct (mapped_B mB HBR) as (MB1 & MB2 & _).
  destruct (seg_B R2 mB ltac:(keep_thru Hfr2; exact A2) ltac:(keep_thru Hfr2; exact A8) ltac:(keep_thru Hfr2; exact A9) ltac:(keep_thru Hfr2; exact A18)
              C120 C132 C80 C172 C56 F40 F48 F56 F64 MB1 MB2)
    as (R3 & Hms3 & B1 & B10 & B11 & B12 & B2 & B8 & B9 & B18 & Hfr3).
  destruct (seg_MS R3 (memC mB) B1 B10 B11 B12 ltac:(unfold memC; repeat apply mapped_wbytes; exact MB2))
    as (R4 & mD & Hms4 & D10 & Hfr4 & Hfill & Hso & Hgr).
  destruct (mD_facts mB mD HBR Hso) as (C196 & G0 & G2 & G4 & G6 & F8 & F16 & F24 & F32).
  destruct (mapped_D mB mD HBR Hgr) as (MD1 & _).
  destruct (seg_C R4 mD ltac:(keep_thru Hfr4; exact B2) ltac:(keep_thru Hfr4; exact B8) ltac:(keep_thru Hfr4; exact B9) ltac:(keep_thru Hfr4; exact B18) F32
              C196 G0 G2 G4 G6 F8 F16 F24 MD1)
    as (R5 & Hms5 & E10 & E2 & E8 & E9 & E18 & Hfr5).
  exists R5, (memE mD).
  split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
    eapply msteps_trans; [exact Hms4 | exact Hms5]. }
  split; [exact E10|]. split; [exact E2|]. split; [exact E8|]. split; [exact E9|].
  assert (K : forall r : reg, reg_in r [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%bv = false -> getr R5 r = getr R1 r).
  { intros r Hr. rewrite Hfr5 by (revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity).
    rewrite Hfr4 by (revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity).
    rewrite Hfr3 by (revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity).
    apply Hfr2. revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity. }
  split; [exact E18|]. split; [rewrite K by reflexivity; exact A19|].
  split; [rewrite K by reflexivity; exact A20|]. split; [rewrite K by reflexivity; exact A21|].
  split; [rewrite K by reflexivity; exact A22|]. split; [rewrite K by reflexivity; exact A23|].
  split; [rewrite K by reflexivity; exact A24|]. split; [rewrite K by reflexivity; exact A25|].
  split; [rewrite K by reflexivity; exact A26|]. split; [rewrite K by reflexivity; exact A27|].
  split.
  { intros r Hr. rewrite K by (revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity).
    apply Hfr1. revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity. }
  exact (post_E mB mD HBR Hfill Hso Hgr).
Qed.

End INIT.
End FXG.
