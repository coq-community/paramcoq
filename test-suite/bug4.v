
Declare ML Module "paramcoq".

Require Import NPeano.
Require Import Omega.

Print BinPosDef.Pos.sub_mask.

Fixpoint sub_mask (xx yy : positive) {struct yy} : BinPosDef.Pos.mask :=
  match xx with
  | (p~1)%positive =>
      match yy with
      | (q~1)%positive => BinPosDef.Pos.double_mask (sub_mask p q)
      | (q~0)%positive => BinPosDef.Pos.succ_double_mask (sub_mask p q)
      | 1%positive => BinPosDef.Pos.IsPos p~0
      end
  | (p~0)%positive =>
      match yy with
      | (q~1)%positive => BinPosDef.Pos.succ_double_mask (sub_mask_carry p q)
      | (q~0)%positive => BinPosDef.Pos.double_mask (sub_mask p q)
      | 1%positive => BinPosDef.Pos.IsPos (BinPosDef.Pos.pred_double p)
      end
  | 1%positive =>
      match yy with
      | (_~1)%positive => BinPosDef.Pos.IsNeg
      | (_~0)%positive => BinPosDef.Pos.IsNeg
      | 1%positive => BinPosDef.Pos.IsNul
      end
  end

with sub_mask_carry (xx yy : positive) {struct yy} : BinPosDef.Pos.mask :=
  match xx with
  | (p~1)%positive =>
      match yy with
      | (q~1)%positive => BinPosDef.Pos.succ_double_mask (sub_mask_carry p q)
      | (q~0)%positive => BinPosDef.Pos.double_mask (sub_mask p q)
      | 1%positive => BinPosDef.Pos.IsPos (BinPosDef.Pos.pred_double p)
      end
  | (p~0)%positive =>
      match yy with
      | (q~1)%positive => BinPosDef.Pos.double_mask (sub_mask_carry p q)
      | (q~0)%positive => BinPosDef.Pos.succ_double_mask (sub_mask_carry p q)
      | 1%positive => BinPosDef.Pos.double_pred_mask p
      end
  | 1%positive => BinPosDef.Pos.IsNeg
  end.

Set Parametricity Debug.
Parametricity Recursive sub_mask.
