(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill DSLayout TreeMem BitsLib STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface DeflateState Trees TreeModel Deflate DeflInitLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 Callee6 TreesApi6 TrInit6 DInit6_M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition A6_TR_INIT : Z := 0x1aa50.
Definition A6_RA_TI : Z := 0x16c24.
Definition A6_RA_RK : Z := 0x16690.
Definition A6_RA_MS : Z := 0x166f4.
Definition A6_ZCALLOC : Z := 0x19ff8.
Definition A6_ZCFREE : Z := 0x1a008.
Definition A6_DATALEN : Z := 0x3a680.

Definition I0 (h wnd prv hd : Z) : simg :=
  [(0, 8%nat, h + 8); (8, 4%nat, 42); (48, 4%nat, 1); (56, 8%nat, 0); (80, 4%nat, 32768); (84, 4%nat, 15);
   (88, 4%nat, 32767); (96, 8%nat, wnd); (112, 8%nat, prv); (120, 8%nat, hd); (132, 4%nat, 32768);
   (136, 4%nat, 15); (140, 4%nat, 32767); (144, 4%nat, 5); (5896, 4%nat, 16384); (5952, 8%nat, 0)]. (* 1.4: high_water at 5952 *)

Lemma ret_ok_zw : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_ok (zw z).
Proof using. intros z Hz H2. apply ret_ok_even. rewrite u_zw_small by lia. exact H2. Qed.

Lemma cell_write_same_at : forall M a b (w : nat) v,
  b = a -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell s6_segs (wbytes M (zw b) (Z_to_le_bytes w v)) a w v.
Proof using. intros M a b w v -> Ha Hw. apply cell_write_same; assumption. Qed.

Section INIT.
Variables (mem : word -> option byte) (h s wnd prv hd pb cb cp n : Z) (sv20 sv21 sv22 sv23 sv24 : word) (raDI : Z).

Variable ZCEIL : Z.
Hypothesis Hh : (0x5c000 <= ZCEIL /\ ZCEIL + 1024 <= h) /\ h + 120 <= 2 ^ 47.
Hypothesis HS : 0 < s /\ s + 5968 <= ZCEIL.
Hypothesis HW : 0 < wnd /\ wnd + 65536 <= ZCEIL.
Hypothesis HP : 0 < prv /\ prv + 65536 <= ZCEIL.
Hypothesis HHD : 0 < hd /\ hd + 65536 <= ZCEIL.
Hypothesis HB : 0 < pb /\ pb + 65536 <= ZCEIL.
Hypothesis HSi : s + 5968 <= 0x10000 \/ 0x5c000 <= s.
Hypothesis HWi : wnd + 65536 <= 0x10000 \/ 0x5c000 <= wnd.
Hypothesis HPi : prv + 65536 <= 0x10000 \/ 0x5c000 <= prv.
Hypothesis HHi : hd + 65536 <= 0x10000 \/ 0x5c000 <= hd.
Hypothesis HBi : pb + 65536 <= 0x10000 \/ 0x5c000 <= pb.
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
Hypothesis HROM : forall x : word, 0x10000 <= bv_unsigned x < 0x293d8 -> mem x = None.
Hypothesis Cra : cell s6_segs mem (h + -8) 8 raDI.
Hypothesis Ccb : cell s6_segs mem (h + -16) 8 cb.
Hypothesis Ccp : cell s6_segs mem (h + -24) 8 cp.
Hypothesis Cn : cell s6_segs mem (h + -32) 8 n.
Hypothesis Cdl : cell s6_segs mem (h + -40) 8 A6_DATALEN.
Hypothesis C20 : cell s6_segs mem (h + -48) 8 (bv_unsigned sv20).
Hypothesis C21 : cell s6_segs mem (h + -56) 8 (bv_unsigned sv21).
Hypothesis C22 : cell s6_segs mem (h + -64) 8 (bv_unsigned sv22).
Hypothesis C23 : cell s6_segs mem (h + -72) 8 (bv_unsigned sv23).
(* 1.4: the prologue also saves s8 (x24) at 0(sp) = h - 80 (`sd s8,0(sp)` at 0x161d4); the epilogue reloads it at 0x16484 *)
Hypothesis C24 : cell s6_segs mem (h + -80) 8 (bv_unsigned sv24).
Hypothesis Z56 : cell s6_segs mem (h + 64) 8 s.
Hypothesis Z64 : cell s6_segs mem (h + 72) 8 A6_ZCALLOC.
Hypothesis Z72 : cell s6_segs mem (h + 80) 8 A6_ZCFREE.
Hypothesis Z80 : cell s6_segs mem (h + 88) 8 0.
Hypothesis Z48 : cell s6_segs mem (h + 56) 8 0.
Hypothesis HI0 : SIMG s6_segs mem s 5968 (I0 h wnd prv hd).
Hypothesis ZW : cells s6_segs mem wnd 1 1 65536 (fun _ => 0).
Hypothesis ZPV : cells s6_segs mem prv 1 1 65536 (fun _ => 0).
Hypothesis ZHD : cells s6_segs mem hd 1 1 65536 (fun _ => 0).
Hypothesis ZPB : cells s6_segs mem pb 1 1 65536 (fun _ => 0).


Definition memA : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
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
    (zw (h + -32)) (Z_to_le_bytes 8 n))       (* 1.4: deflateReset also saves s2 (`sd s2,0(sp)` at 0x16624) *)
    (zw (h + -40)) (Z_to_le_bytes 8 91792))
    (zw (h + -48)) (Z_to_le_bytes 8 (h + 8)))
    (zw (h + -56)) (Z_to_le_bytes 8 cp))
    (zw (h + -64)) (Z_to_le_bytes 8 n))       (* 1.4: deflateResetKeep also saves s2 (`sd s2,0(sp)` at 0x16ae4) *)
    (zw (h + 48)) (Z_to_le_bytes 8 0))
    (zw (h + 56)) (Z_to_le_bytes 8 0))
    (zw (h + 24)) (Z_to_le_bytes 8 0))
    (zw (h + 96)) (Z_to_le_bytes 4 2))
    (zw (s + 32)) (Z_to_le_bytes 8 pb))
    (zw (s + 40)) (Z_to_le_bytes 8 0))
    (zw (s + 8)) (Z_to_le_bytes 4 42))
    (zw (h + 104)) (Z_to_le_bytes 8 1))
    (zw (s + 56)) (Z_to_le_bytes 8 0))        (* 1.4: `sd zero,56(s0)` at 0x16ba4 *)
    (zw (s + 76)) (Z_to_le_bytes 4 (-2)).

Definition iC : cfg := CFG [] [] [EVar 45%nat] [0x1aa50; 0x27c04] [].

Lemma seg_A : forall regs,
  getr regs 2 = zw (h + -80) -> getr regs 8 = zw (h + 8) -> getr regs 9 = zw s -> getr regs 10 = zw pb ->
  getr regs 20 = zw (s + 5888) -> getr regs 18 = zw 0 -> getr regs 19 = zw 6 -> getr regs 21 = zw 1 ->
  getr regs 22 = zw 15 -> getr regs 23 = zw 8 ->
  exists R,
    msteps s6_segs (mkst regs (0x16468 : word) mem s6_rom) (mkst R (0x1aa50 : word) memA s6_rom)
    /\ getr R 1 = zw A6_RA_TI /\ getr R 10 = zw s /\ getr R 2 = zw (h + -64) /\ getr R 8 = zw s /\ getr R 9 = zw (h + 8)
    /\ getr R 18 = zw 0 (* 1.4: deflateResetKeep sets s2 = 0 (`li s2,0` at 0x16b94; level 6 skips the reload) *)
    /\ getr R 19 = zw A6_DATALEN /\ getr R 20 = sv20 /\ getr R 21 = sv21 /\ getr R 22 = sv22 /\ getr R 23 = sv23
    /\ getr R 24 = sv24
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24]%bv = false -> getr R r = getr regs r).
Proof using HI0 Z72 Z64 Z56 C24 C23 C22 C21 C20 Cdl Cn Ccp Ccb Cra MS MK HraDI Hn Hcp Hcb HB HHD HP HW HS Hh ZCEIL hd prv wnd.   (* 1.4: + C24, the s8 slot the epilogue reloads *)
  intros regs P2 P8 P9 P10 P20 P18 P19 P21 P22 P23.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB.
  pose proof (SIMG_cell_in s6_segs mem s 5968 _ 5896 4 16384 HI0 ltac:(cbn; tauto)) as F5896.
  pose proof (SIMG_cell_in s6_segs mem s 5968 _ 96 8 wnd HI0 ltac:(cbn; tauto)) as F96.
  pose proof (SIMG_cell_in s6_segs mem s 5968 _ 112 8 prv HI0 ltac:(cbn; tauto)) as F112.
  pose proof (SIMG_cell_in s6_segs mem s 5968 _ 120 8 hd HI0 ltac:(cbn; tauto)) as F120.
  pose proof (SIMG_cell_in s6_segs mem s 5968 _ 0 8 (h + 8) HI0 ltac:(cbn; tauto)) as Fs0.
  pose proof Fs0 as Fs0'. rewrite Z.add_0_r in Fs0'.
  pose proof (SIMG_cell_in s6_segs mem s 5968 _ 8 4 42 HI0 ltac:(cbn; tauto)) as F8.
  pose proof (SIMG_cell_in s6_segs mem s 5968 _ 48 4 1 HI0 ltac:(cbn; tauto)) as F48.
  unfold mapped in MK, MS. unfold A6_DATALEN, A6_ZCALLOC, A6_ZCFREE in *.
  pose proof (u64_range sv20) as U20. pose proof (u64_range sv21) as U21. pose proof (u64_range sv22) as U22. pose proof (u64_range sv23) as U23.
  pose proof (u64_range sv24) as U24.
  (* 1.4 path: four pointer checks, the 10-slot epilogue, deflateReset's prologue, deflateResetKeep's inlined state check
     (status 42: the mask test branches to the 666 / 42 compares), wrap 1, adler32(0, NULL, 0), level 6 != 0, then _tr_init *)
  symex s6_segs iC 120%nat [false; false; false; false; false; false; false; false; false; true; false; true; true; false; false; true; true; true]
    [RVal (ELit 16384); RVal (EVar 34); RVal (EVar 35); RVal (EVar 36);
     RVal (EVar 45); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (ELit 0x3a680); RVal (EVar 41); RVal (EVar 42); RVal (EVar 43); RVal (EVar 44);
     RVal (EVar 46);
     RVal (ELit 0x19ff8); RVal (ELit 0x1a008); RVal (EVar 33); RVal (EAdd (EVar 32) (ELit 8)); RVal (ELit 42); RVal (ELit 1)]
    [(2, EAdd (EVar 32) (ELit (-80))); (8, EAdd (EVar 32) (ELit 8)); (9, EVar 33); (10, EVar 37); (20, EAdd (EVar 33) (ELit 5888));
     (18, ELit 0); (19, ELit 6); (21, ELit 1); (22, ELit 15); (23, ELit 8)]
    [(32%nat, 2^47); (33%nat, 2^47); (34%nat, 2^47); (35%nat, 2^47); (36%nat, 2^47); (37%nat, 2^47); (38%nat, 2^63); (39%nat, 2^63); (40%nat, 2^63);
     (41%nat, 2^64); (42%nat, 2^64); (43%nat, 2^64); (44%nat, 2^64); (45%nat, 2^64); (46%nat, 2^64)] NoRegions
    [h; s; wnd; prv; hd; pb; cb; cp; n; bv_unsigned sv20; bv_unsigned sv21; bv_unsigned sv22; bv_unsigned sv23; raDI; bv_unsigned sv24] NoVals F0 F0'
    (mkst regs (0x16468 : word) mem s6_rom) R HR Hfr Hms.
  all: try (symex_auto; lia).
  exists R. split; [exact Hms|].
  symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (2%bv : reg) as A2. symex_reg HR (8%bv : reg) as A8.
  symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18. symex_reg HR (19%bv : reg) as A19.
  symex_reg HR (20%bv : reg) as A20. symex_reg HR (21%bv : reg) as A21. symex_reg HR (22%bv : reg) as A22. symex_reg HR (23%bv : reg) as A23.
  symex_reg HR (24%bv : reg) as A24.
  unfold A6_RA_TI. rewrite ?zw_u in *.
  split; [exact A1|]. split; [exact A10|]. split; [exact A2|]. split; [exact A8|]. split; [exact A9|].
  split; [exact A18|]. split; [exact A19|]. split; [exact A20|]. split; [exact A21|]. split; [exact A22|]. split; [exact A23|].
  split; [exact A24|].
  intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.



Definition IA : simg :=
  simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put (simg_put
    (I0 h wnd prv hd) 16 8 pb) 24 8 65536) 196 4 6) 200 4 0) 5888 8 (pb + 16384)) 5904 4 49149) 72 1 8)
    32 8 pb) 40 8 0) 8 4 42) 56 8 0) 76 4 (-2).   (* 1.4: s + 56 cleared at 0x16ba4 *)

Local Ltac simg_tower H0 :=
  lazymatch goal with
  | |- SIMG _ (wbytes ?M (zw (s + ?o)) (Z_to_le_bytes ?w ?v)) _ _ _ =>
      eapply (SIMG_store s6_segs M s 5968 _ o w v); [simg_tower H0 | vm_compute; reflexivity | lia | lia]
  | |- SIMG _ (wbytes ?M (zw ?b) ?bs) _ _ _ =>
      eapply (SIMG_ext s6_segs M); [simg_tower H0 | intros z Hz; change (Z_to_bv 64 z) with (zw z); apply wbytes_inside; rewrite ?length_Z_to_le_bytes; [lia | cbn; lia | rewrite u_zw_small by lia; cbn; lia] ]
  | |- SIMG _ mem _ _ _ => exact H0
  end.

Lemma simg_A : SIMG s6_segs memA s 5968 IA.
Proof using HI0 HS Hh ZCEIL.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB HraDI.
  unfold memA, IA. simg_tower HI0.
Qed.

Definition GA : franges := [(s, 5968); (h + -80, 80); (h + 8, 104)].

Local Ltac ag_tower H0 :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold GA;
              first [ apply sub_franges_here; cbn; lia | apply sub_franges_later; apply sub_franges_here; cbn; lia
                    | do 2 apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact H0.

Lemma agree_A : agree_out GA mem memA.
Proof using HS Hh ZCEIL.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB HraDI.
  unfold memA. ag_tower (agree_out_refl GA mem).
Qed.

Lemma grows_A : forall x, mem x <> None -> memA x <> None.
Proof using. intros x Hx. unfold memA. repeat apply wbytes_grows. exact Hx. Qed.

Lemma mapped_A : forall a k, mapped mem a k -> mapped memA a k.
Proof using. intros a k H x Hx. apply grows_A. exact (H x Hx). Qed.

Lemma cells_A : forall P N f, cells s6_segs mem P 1 1 N f -> 0 <= P -> P + N <= 2 ^ 64 ->
  (s + 5968 <= P \/ P + N <= s) -> (h + 112 <= P \/ P + N <= h + -80) -> cells s6_segs memA P 1 1 N f.
Proof using HS Hh ZCEIL.
  intros P N f Hc HP0 HP1 D1 D2. pose proof agree_A as AG.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB MK MS HI0 HraDI.
  apply (cells_agree_out s6_segs GA mem memA P 1 1%nat N f AG); [| lia | lia | lia | exact Hc].
  unfold GA. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; lia.
Qed.

Lemma cellsA :
  cell s6_segs memA (h + -8) 8 raDI /\ cell s6_segs memA (h + -16) 8 cb /\ cell s6_segs memA (h + -24) 8 cp
  /\ cell s6_segs memA (h + -40) 8 A6_RA_RK /\ cell s6_segs memA (h + -48) 8 (h + 8) /\ cell s6_segs memA (h + -56) 8 cp
  /\ cell s6_segs memA (h + 48) 8 0 /\ cell s6_segs memA (h + 56) 8 0 /\ cell s6_segs memA (h + 24) 8 0
  /\ cell s6_segs memA (h + 96) 4 2 /\ cell s6_segs memA (h + 104) 8 1
  /\ cell s6_segs memA (h + 64) 8 s /\ cell s6_segs memA (h + 72) 8 A6_ZCALLOC /\ cell s6_segs memA (h + 80) 8 A6_ZCFREE
  /\ cell s6_segs memA (h + 88) 8 0.
Proof using Z80 Z72 Z64 Z56 HS Hh ZCEIL.
  clear HSi HWi HPi HHi HBi DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB HraDI.
  unfold memA, A6_RA_RK, A6_ZCALLOC, A6_ZCFREE in *.
  repeat split;
    repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                  | apply cell_write_other; [| lia | cbn; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia] ]);
    assumption.
Qed.


Definition p6 : ds_ptrs := DSP (h + 8) wnd prv hd pb.
Definition FTR : franges := [(s, 5968); (pb, 65536)].

Variables (b0 bw bp bh bb : blk) (cs : cstrm).
Local Abbreviation sRK0 := (DInit6_M.sRK0 b0 bw bp bh bb cs).
Local Abbreviation sTI0 := (DInit6_M.sTI0 b0 bw bp bh bb cs).
Local Abbreviation sLM0 := (DInit6_M.sLM0 b0 bw bp bh bb cs).

Lemma BRH_FTR : BRH FTR s p6 65536.
Proof using DSB HB HS Hh ZCEIL.
  clear - Hh HS HB DSB. unfold BRH, FTR, p6, dsl_SIZE. cbn [p_pending_buf].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply sub_franges_here; lia|]. split; [apply sub_franges_here; lia|]. split; [apply sub_franges_here; lia|].
  apply sub_franges_later. apply sub_franges_here; lia.
Qed.

Lemma FTR_S : sub_franges FTR s dsl_SIZE.
Proof using. clear. unfold FTR, dsl_SIZE. apply sub_franges_here; lia. Qed.

Lemma fields_RK : fields s6_segs memA s dsl_layout (dvals6 sRK0 p6 s (0, 0, 0, 0, 0, 0)).
Proof using HI0 HS Hh ZCEIL.
  pose proof simg_A as SA. clear - SA.
  rewrite (sRK0_dvals b0 bw bp bh bb cs p6 s). unfold p6. cbn [p_strm p_pending_buf p_window p_prev p_head].
  apply (fields_eqm_transfer s6_segs memA s dsl_layout (simg_vals IA dsl_layout)).
  - apply (SIMG_fields s6_segs memA s 5968 IA dsl_layout SA). vm_compute. reflexivity.
  - unfold IA, I0. rewrite ?Z.add_0_r. set (vh := h + 8). set (vpb := pb + 16384).
    lazy -[Z.modulo Z.pow vh vpb]. repeat split; reflexivity.
Qed.

Lemma arrays_RK : dsl_arrays s6_segs memA s sRK0.
Proof using HI0 HS Hh ZCEIL hd prv wnd.
  pose proof simg_A as SA. clear - Hh SA HS.
  pose proof (sRK0_arrs b0 bw bp bh bb cs) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & _).
  unfold dsl_arrays. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9.
  repeat match goal with |- _ /\ _ => split end;
    (lazymatch goal with |- cells _ _ _ _ _ ?n _ => let k := eval vm_compute in (Z.to_nat n) in change n with (Z.of_nat k) end;
     eapply cells_extf; [ eapply (SIMG_cells_z s6_segs memA s 5968 IA); [exact SA | vm_compute; reflexivity | lia | cbn; lia | cbn; lia]
                        | intros i Hi; symmetry; first [apply arr_u16_of_z0 | apply arr_s32_of_z0 | apply arr_u8_of_z0] ]).
Qed.

Lemma pend_RK : cells s6_segs memA pb 1 1 65536 (arr_get (ds_pending_buf sRK0)).
Proof using ZPB DPH DWH DWP DSB HB HHD HP HW HS Hh ZCEIL hd prv wnd.
  clear HraDI.
  pose proof (sRK0_arrs b0 bw bp bh bb cs) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E & _). rewrite E.
  eapply cells_extf; [| intros i Hi; symmetry; apply blk_bytes_z0].
  apply (cells_A pb 65536 (fun _ => 0) ZPB); [lia | lia | exact DSB | clear - Hh HB; lia].
Qed.

Lemma BRi_RK : BRi6 FTR memA s p6 65536 memA sRK0.
Proof using ZPB HI0 MB MS DPH DWH DWP DSB HB HHD HP HW HS Hh ZCEIL.
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
    msteps s6_segs (mkst regs (0x1aa50 : word) memA s6_rom) (mkst R (0x16c24 : word) mB s6_rom)
    /\ BR6 FTR memA s p6 65536 mB sTI0
    /\ (forall r : reg, reg_in r TI_CLOB = false -> getr R r = getr regs r).
Proof using ZPB HI0 MB MS DPH DWH DWP DSB HB HHD HP HW HS Hh ZCEIL.
  intros regs P10 P1. pose proof BRH_FTR as HL. pose proof FTR_S as HFS. pose proof BRi_RK as HBRi.
  clear - P10 P1 HL HFS HBRi.
  destruct (tr_init_run6_ok FTR memA memA s p6 65536 sRK0 (zw A6_RA_TI) regs HL HFS
              ltac:(unfold A6_RA_TI; apply ret_ok_zw; [lia | reflexivity]) HBRi P10 P1) as (R & mB & Hms & HBR & Hfr).
  exists R, mB. unfold TrInit6.A6_TR_INIT, A6_RA_TI in *.
  replace (zw 0x1aa50) with (0x1aa50%bv : word) in Hms by (apply bv_eq; reflexivity).
  replace (zw 0x16c24) with (0x16c24%bv : word) in Hms by (apply bv_eq; reflexivity).
  split; [exact Hms|]. split; [rewrite (sTI0_eq b0 bw bp bh bb cs); exact HBR | exact Hfr].
Qed.

End INIT.
End FXG.
