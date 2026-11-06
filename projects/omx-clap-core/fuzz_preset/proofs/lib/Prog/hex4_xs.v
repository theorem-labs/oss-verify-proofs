(* Theorem Labs, 2026-10: statement of hex4's asan / asan-ubsan walk in the cgif donor's program-walk form, running-journal shape (YCbh.v tlzw_specX) over YCbqG's journal layer (ajournal_x); result facts over lib/Spec/PjGrammar.v's hexval / hex4, as preset's released plain contract lib/Prog/hex4_c.v states them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v YI00 YI0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint hacc (v : Z) (l : list Z) : option Z :=
match l with
| [] => Some v
| c :: r => match PjGrammar.hexval c with Some d => hacc (16 * v + d) r | None => None end
end.
Lemma hacc_hex4 : forall l, Z.of_nat (length l) = 4 -> hacc 0 l = PjGrammar.hex4 l.
Proof.
intros l Hl.
destruct l as [|a [|b [|c [|d [|e l]]]]]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Hl; try lia.
cbn [hacc PjGrammar.hex4].
destruct (PjGrammar.hexval a) as [va|]; [|reflexivity].
destruct (PjGrammar.hexval b) as [vb|]; [|destruct (PjGrammar.hexval c); reflexivity].
destruct (PjGrammar.hexval c) as [vc|]; [|reflexivity].
destruct (PjGrammar.hexval d) as [vd|]; [|reflexivity].
cbn. f_equal. lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Definition HEX4_STK : Z := 16.
Definition thex4_leaf_postX (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z)
(W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (Hpc : list Z) (W : world segs) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (o : Z) (BS : list Z) : world segs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
aregs_preserved regs regs' /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - HEX4_STK <= x < spZ regs) -> ~ (o <= x < o + 4) ->
aview segs (w_H W) mem' x = aview segs (w_H W) memc x) /\
match PjGrammar.hex4 BS with
| Some h => getr regs' 10 = w64 0 /\ val_mem segs (mrestrict (w_H W) mem') o 4 h
| None => getr regs' 10 = w64 (-1) /\
(forall x, o <= x < o + 4 -> aview segs (w_H W) mem' x = aview segs (w_H W) memc x)
end.
Definition thex4_leafX (a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (p o : Z) (BS : list Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 10 = w64 p -> getr regs 11 = w64 o ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - HEX4_STK -> spZ regs <= sp0 ->
(forall x, spZ regs - HEX4_STK <= x < spZ regs -> apresent (w_H W) memc x) ->
4096 <= p -> amem_range p 4 -> range_addressable (aview segs (w_H W) memc) SHADOW_OFF p 4 ->
garr8 segs (mrestrict (w_H W) memc) p BS -> Z.of_nat (length BS) = 4 ->
spZ regs <= o -> o + 4 <= sp0 -> o mod 4 = 0 -> range_addressable (aview segs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(o + 4 <= p \/ p + 4 <= o) ->
(spZ regs <= p \/ p + 4 <= spZ regs - HEX4_STK) ->
SRr segs W (cfg_at segs a regs memc mdc)
(thex4_leaf_postX STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc k regs o BS).
End b.
