export type MalType = MalAtom | MalList | MalFunc
export type MalAtom = MalNil | MalNumber | MalSymbol | MalBoolean

export const enum MalTypes {
    List = 1,
    Number, 
    Symbol,
    Nil,
    Boolean,
    Function, 
}

export class MalNumber {
    type = MalTypes.Number
    value: number

    constructor(value: number) {
        this.value = value
    }
}

export class MalSymbol {
    type = MalTypes.Symbol
    value: string

    constructor(value: string) {
        this.value = value
    }
}

export class MalNil {
    type = MalTypes.Nil
}

export class MalBoolean {
    type = MalTypes.Boolean
    value: Boolean

    constructor(value: Boolean) {
        this.value = value
    }
}

export class MalList {
    type = MalTypes.List
    list: Array<MalType>

    constructor(list: Array<MalType>) {
        this.list = list
    }

    // just for brevity
    push(data: MalType) {
        this.list.push(data)
    }
}

export class MalFunc {
    type = MalTypes.Function
    f: (...args: (MalType)[]) => MalType
    
    constructor(f: (...args: (MalType | undefined)[]) => MalType) {
        this.f = f
    }

    apply(args: MalList): MalType {
        return this.f.apply(null, args.list)  
    }
}
