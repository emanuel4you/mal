module Mal
  module Types
    class List < ::Array; end
    class Vector < ::Array; end
    class Hashmap < ::Hash; end

    class Base < ::Struct.new(:value)
      def inspect
        value.inspect
      end
    end

    class String < Base; end

    class Atom < Base
      def inspect
        "Atom<#{value.inspect}>"
      end
    end

    class Keyword < Base
      def self.for(value)
        @_keywords ||= {}

        if @_keywords.key?(value)
          @_keywords[value]
        else
          @_keywords[value] = new(value)
        end
      end
    end

    class Number < Base
      def +(other)
        self.class.new(value + other.value)
      end

      def -(other)
        self.class.new(value - other.value)
      end

      def *(other)
        self.class.new(value * other.value)
      end

      def /(other)
        self.class.new(value / other.value)
      end
    end

    class Symbol < Base
      def self.for(value)
        @_symbols ||= {}

        if @_symbols.key?(value)
          @_symbols[value]
        else
          @_symbols[value] = new(value)
        end
      end

      def inspect
        value
      end
    end

    class Nil < Base
      def self.instance
        @_instance ||= new(nil)
      end

      def inspect
        "nil"
      end
    end

    class True < Base
      def self.instance
        @_instance ||= new(true)
      end
    end

    class False < Base
      def self.instance
        @_instance ||= new(false)
      end
    end

    class Callable
      def initialize(&block)
        @fn = block
      end

      def call(args)
        @fn.call(args)
      end

      def inspect
        raise NotImplementedError
      end
    end

    class Builtin < Callable
      def inspect
        "#<builtin>"
      end

      def is_mal_fn?
        false
      end
    end

    class Function < Callable
      attr_reader :ast, :params, :env

      def initialize(ast, params, env, &block)
        @ast = ast
        @params = params
        @env = env
        @fn = block
      end

      def inspect
        "#<function>"
      end

      def is_mal_fn?
        true
      end
    end
  end
end
