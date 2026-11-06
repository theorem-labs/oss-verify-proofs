(* LeafCgKit: the ONE shared interface for decode image B's program-leaf translations (footprint walk ->
   cgif_file leaf form). Port of fuzz_decode to the released cgif_file_fuzzer structure (the port recipe,
   sec. 3).
   * cgif names are Section Variables named exactly as in cgif_file_fuzzer (origin/ossv/recipes c8557374ad2e,
     proofs/cgif/cgif_file_fuzzer/lib/<file>:<line> in the comments); when a Theorem Labs lane's relocated core lands they become
     the core's names (a rename).
   * Small cgif definitions are copied verbatim (marked), at segs := rsegs and the unit's asyms B.
   * The cgif FACTS the leaf translations need are stated once below as `_stmt` Props (each the text of, or a direct
     consequence of, a cgif lemma, cited), and taken as Section hypotheses by the proofs until the core lands.
   * `leaf_cg_of_evtF_stmt` is the ONE generic translation every leaf proof applies (proof: LeafCgGlue.v). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import MState Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require ExecF PropExec.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* ---- cgif definitions copied verbatim (YG0d.v:18, :19-24, :27, :212-213; YG0n.v:27; YK04.v:43-46;
   YK04R.v:130 fp_avoids at decode's ExecF.footprint), at segs := rsegs ---- *)
Definition ESTACK : Z := 4096.
Definition acallee_saved (r : Z) : Prop :=
  r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27).
Definition aregs_preserved (regs regs' : bvmap 5 word) : Prop :=
  forall r, acallee_saved r -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r).
Definition spZ (regs : bvmap 5 word) : Z := bv_unsigned (YK11.getr regs (Z_to_bv 5 2)).
Definition raZ (regs : bvmap 5 word) : Z := bv_unsigned (YK11.getr regs (Z_to_bv 5 1)).
Definition w64 (z : Z) : word := Z_to_bv 64 z.
Definition cfg_at {fx : YK11.FPState} (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
  mkCfg (YK11.mkst regs (w64 pc) mem (YK11.seg_rom rsegs)) md.
Definition apresent (H : word -> bool) (mem : word -> option byte) (a : Z) : Prop :=
  H (Z_to_bv 64 a) = false /\ exists b, mem (Z_to_bv 64 a) = Some b.
Definition woff (a : word) (k : nat) : word := Z_to_bv 64 (bv_unsigned a + Z.of_nat k).
Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop :=
  forall k, (k < n)%nat -> H (woff a k) = false.
Definition fp_avoids (H : word -> bool) (RNG : ExecF.footprint) : Prop :=
  forall (a : word) (n : nat), RNG (bv_unsigned a) n -> range_avoids H a n.
Definition in_wr (WR : list (Z * Z)) (x : Z) : Prop := Exists (fun p => fst p <= x < snd p) WR.
(* YG0d.v in_img (verbatim, segs := rsegs): x lies in a loaded segment of the image. *)
Definition in_img (a : Z) : Prop :=
  exists sg, In sg rsegs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).

(* The machine state decode's footprint contracts start from, read off cgif's (regs, mem): decode's MS / mkR form. *)
Definition ms_of_regs {fx : YK11.FPState} (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) : machine_state :=
  MS (mkR (YK11.getr regs (Z_to_bv 5 1)) (YK11.getr regs (Z_to_bv 5 2)) (YK11.getr regs (Z_to_bv 5 3)) (YK11.getr regs (Z_to_bv 5 4)) (YK11.getr regs (Z_to_bv 5 5)) (YK11.getr regs (Z_to_bv 5 6)) (YK11.getr regs (Z_to_bv 5 7)) (YK11.getr regs (Z_to_bv 5 8)) (YK11.getr regs (Z_to_bv 5 9)) (YK11.getr regs (Z_to_bv 5 10)) (YK11.getr regs (Z_to_bv 5 11)) (YK11.getr regs (Z_to_bv 5 12)) (YK11.getr regs (Z_to_bv 5 13)) (YK11.getr regs (Z_to_bv 5 14)) (YK11.getr regs (Z_to_bv 5 15)) (YK11.getr regs (Z_to_bv 5 16)) (YK11.getr regs (Z_to_bv 5 17)) (YK11.getr regs (Z_to_bv 5 18)) (YK11.getr regs (Z_to_bv 5 19)) (YK11.getr regs (Z_to_bv 5 20)) (YK11.getr regs (Z_to_bv 5 21)) (YK11.getr regs (Z_to_bv 5 22)) (YK11.getr regs (Z_to_bv 5 23)) (YK11.getr regs (Z_to_bv 5 24)) (YK11.getr regs (Z_to_bv 5 25)) (YK11.getr regs (Z_to_bv 5 26)) (YK11.getr regs (Z_to_bv 5 27)) (YK11.getr regs (Z_to_bv 5 28)) (YK11.getr regs (Z_to_bv 5 29)) (YK11.getr regs (Z_to_bv 5 30)) (YK11.getr regs (Z_to_bv 5 31)))
     fp_regs (w64 pc) fp_csr None mem (YK11.seg_rom rsegs).

(* decode's lib/Lib/PropExec.v and YK11 define getr / seg_rom with the same bodies: the footprint contracts use the
   former, the cgif side the latter. *)
Lemma seg_rom_eq : PropExec.seg_rom = YK11.seg_rom.
Proof. reflexivity. Qed.
Lemma getr_eq : PropExec.getr = YK11.getr.
Proof. reflexivity. Qed.

Section LeafCgKit.
Context {fx : YK11.FPState}.
Variable world : Type.                                                (* YA0n.v:17 Record world *)
Variable w_H : world -> word -> bool.                                 (* YA0n.v:18 field w_H *)
Variable SRr : world -> config -> (world -> config -> Prop) -> Prop.    (* YA0n.v:34 *)
Variable alayout : Type.                                              (* YG0f.v:42 *)
Variable astate : Type.                                               (* YG00.v:153 *)
Variable AR : alayout -> astate -> world -> (word -> option byte) -> Model -> Prop.  (* YG0n.v:489, at B *)
Variable aview : (word -> bool) -> (word -> option byte) -> Z -> option Z.          (* YG0n.v:17 *)
Variable same_but_materialized : Model -> Model -> Prop.              (* YK04.v:538 *)
Variable ly_stk_lo ly_stk_hi : alayout -> Z.                          (* YG0f.v alayout fields *)
Variable ret_ok : word -> Prop.                                       (* YK0s.v:192 *)
Variable as_gp as_tp : Z.                                             (* asyms B fields *)
Variable aowned : alayout -> astate -> Z -> Prop.                     (* YG0n.v:235, at B *)

(* ecall_pre, verbatim body of YG0d.v:277-283 over the names above. *)
Definition ecall_pre (ly : alayout) (S : astate) (W : world) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  AR ly S W mem md /\
  ret_ok (YK11.getr regs (Z_to_bv 5 1)) /\
  spZ regs mod 16 = 0 /\ ly_stk_lo ly + ESTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
  (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
  YK11.getr regs (Z_to_bv 5 3) = w64 as_gp /\ YK11.getr regs (Z_to_bv 5 4) = w64 as_tp.

(* The footprint the call site picks: every range of visible bytes; fp_avoids (w_H W) (RNG_W W) holds by identity
   (up to Z_to_bv 64 (bv_unsigned a) = a). *)
Definition RNG_W (W : world) : ExecF.footprint := fun b n => range_avoids (w_H W) (Z_to_bv 64 b) n.

(* The cgif leaf post (shape of A/AE39.v:46 amemchr0_realizesM). *)
Definition dleaf_post (ly : alayout) (S : astate) (W : world) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (RES : option Z) (WR : list (Z * Z)) (X : (word -> option byte) -> Prop)
    : world -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at (raZ regs) regs' mem' md' /\
    AR ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    (forall r, RES = Some r -> YK11.getr regs' (Z_to_bv 5 10) = w64 r) /\
    (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - ESTACK <= x < spZ regs) ->
       ~ in_wr WR x -> aview (w_H W) mem' x = aview (w_H W) mem x) /\
    (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x) /\
    X mem'.

(* ---- the cgif facts, stated once ---- *)
(* SRr_fevt (a Theorem Labs lane, lib/Reusable/YA0nR.v on a working branch eea54967566) with its fsteps run read
   as decode's ExecF.mstepsF (ExecF.mstepF is YK04R.fstep's body; glue fsteps_of_mstepsF / fevt_of_evtF). *)
Definition bridge_evtF_stmt : Prop :=
  forall (W : world) ms model (RNG : ExecF.footprint) (P : machine_state -> Prop) (Q : world -> config -> Prop),
    ExecF.evtF rsegs RNG P ms -> fp_avoids (w_H W) RNG ->
    (forall ms' model', P ms' -> same_but_materialized model model' -> SRr W (mkCfg ms' model') Q) ->
    SRr W (mkCfg ms model) Q.
(* YA0n.v:39 SRr_ret (found missing by a Theorem Labs lane's glue lane: without it no kit fact concludes SRr from its post). *)
Definition SRr_ret_stmt : Prop := forall (W : world) (c : config) (Q : world -> config -> Prop), Q W c -> SRr W c Q.
(* YG0d.v:437 AR_frame_law at md' = md (the in_band_rw condition taken for every hidden byte, which implies it). *)
Definition AR_frame_stmt : Prop :=
  forall ly S W mem md mem', AR ly S W mem md ->
    (forall a, 0 <= a < 2 ^ 64 -> aowned ly S a -> aview (w_H W) mem' a = aview (w_H W) mem a) ->
    (forall a, aview (w_H W) mem a <> None -> aview (w_H W) mem' a <> None) ->
    (forall a : word, w_H W a = true -> mem' a = mem a) ->
    AR ly S W mem' md.
(* YG0d.v AR_stack_law. *)
Definition AR_stack_stmt : Prop :=
  forall ly S W mem md a, AR ly S W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned ly S a.
(* A/AD1y.v:139 AR_same_but_materialized. *)
Definition AR_sbm_stmt : Prop :=
  forall ly S W mem md md', AR ly S W mem md -> same_but_materialized md md' -> AR ly S W mem md'.
(* From YG0n.v:17's body (aview H mem a = option_map bv_unsigned (mbyte segs (mrestrict H mem) a)). *)
Definition aview_ext_stmt : Prop :=
  forall H mem mem' a, mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview H mem' a = aview H mem a.
Definition aview_some_stmt : Prop :=
  forall H mem a, H (Z_to_bv 64 a) = false -> mem (Z_to_bv 64 a) <> None -> aview H mem a <> None.
(* From YK0s.v:192 (ret_ok k := v_jalr k 0 = k) and decode's MState.ret_pc (bit 0 cleared). *)
Definition ret_ok_stmt : Prop := forall k, ret_ok k -> ret_pc k = k.

(* ---- the ONE generic translation (proof: LeafCgGlue.v) ---- *)
Definition leaf_cg_of_evtF_stmt : Prop :=
  forall ly S W regs mem md (PC K : Z) (P : machine_state -> Prop) (WR : list (Z * Z)) (RES : option Z)
         (X : (word -> option byte) -> Prop),
    ecall_pre ly S W regs mem md ->
    0 <= K <= ESTACK ->
    (forall x, in_wr WR x -> 0 <= x < 2 ^ 64 /\ w_H W (Z_to_bv 64 x) = false /\ ~ aowned ly S x /\ ~ in_img x) ->
    ExecF.evtF rsegs (RNG_W W) P (ms_of_regs PC regs mem) ->
    (forall ms', P ms' -> exists regs' mem',
       ms' = MS regs' fp_regs (ret_pc (YK11.getr regs (Z_to_bv 5 1))) fp_csr None mem' (YK11.seg_rom rsegs) /\
       munch ((spZ regs - K, spZ regs) :: WR) mem mem' /\
       (forall x, (spZ regs - K <= x < spZ regs \/ in_wr WR x) -> exists b, mrd rsegs mem' (Z_to_bv 64 x) = Some b) /\
       aregs_preserved regs regs' /\
       (forall r, RES = Some r -> YK11.getr regs' (Z_to_bv 5 10) = w64 r) /\
       X mem') ->
    SRr W (cfg_at PC regs mem md) (dleaf_post ly S W regs mem md RES WR X).

(* The float-state-changing variant (reac_braid_encode): the return keeps fp_csr and every float register but
   f10..f15, stated in cgif's exists-fx' form (lib/YL0g.v:58-64). *)
Definition dleaf_post_fx (ly : alayout) (S : astate) (W : world) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (WR : list (Z * Z)) (X : (word -> option byte) -> Prop) : world -> config -> Prop :=
  fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (raZ regs)) mem' (YK11.seg_rom rsegs)) md' /\
    @fp_csr fx' = @fp_csr fx /\
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get (@fp_regs fx') k = reg_get (@fp_regs fx) k) /\
    AR ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - ESTACK <= x < spZ regs) ->
       ~ in_wr WR x -> aview (w_H W) mem' x = aview (w_H W) mem x) /\
    (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x) /\
    X mem'.
Definition leaf_cg_of_evtF_fx_stmt : Prop :=
  forall ly S W regs mem md (PC K : Z) (P : machine_state -> Prop) (WR : list (Z * Z))
         (X : (word -> option byte) -> Prop),
    ecall_pre ly S W regs mem md ->
    0 <= K <= ESTACK ->
    (forall x, in_wr WR x -> 0 <= x < 2 ^ 64 /\ w_H W (Z_to_bv 64 x) = false /\ ~ aowned ly S x /\ ~ in_img x) ->
    ExecF.evtF rsegs (RNG_W W) P (ms_of_regs PC regs mem) ->
    (forall ms', P ms' -> exists regs' F' mem',
       ms' = MS regs' F' (ret_pc (YK11.getr regs (Z_to_bv 5 1))) fp_csr None mem' (YK11.seg_rom rsegs) /\
       (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get F' k = reg_get fp_regs k) /\
       munch ((spZ regs - K, spZ regs) :: WR) mem mem' /\
       (forall x, (spZ regs - K <= x < spZ regs \/ in_wr WR x) -> exists b, mrd rsegs mem' (Z_to_bv 64 x) = Some b) /\
       aregs_preserved regs regs' /\
       X mem') ->
    SRr W (cfg_at PC regs mem md) (dleaf_post_fx ly S W regs mem md WR X).
End LeafCgKit.
